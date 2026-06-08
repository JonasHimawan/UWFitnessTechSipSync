#include <HX711.h>
#include <Preferences.h>
#include <Adafruit_MPU6050.h>
#include <Adafruit_Sensor.h>
#include <Wire.h>
#include <Adafruit_NeoPixel.h>

#include <BLEDevice.h>
#include <BLEServer.h>
#include <BLEUtils.h>
#include <BLE2902.h>

// ============================================================
// SipSync Smart Bottle - Version 4
// ============================================================
// New since V3:
//   - Runtime BLE name SipSync-XXXX from eFuse MAC (was hardcoded)
//   - 'r' command: re-tare load cell, persists to NVS, keeps cal factor
//   - Soft idle power state with motion-wake (slows polling, dims LEDs)
//   - Brownout-safe LED ramp on boot; default brightness lowered to 30
//   - Persistent lifetime sip totals (NVS-backed)
//   - Battery voltage telemetry (needs divider on D1 / GPIO3)
//   - Configurable sip / tilt / brightness over BLE (s / i / b commands)
//
// Menu:
//   m   = show menu
//   1   = calibrate (USB Serial only)
//   t   = sip tracker mode
//   r   = re-tare load cell (keeps calibration factor)
//   c   = clear lifetime stats
//   p   = print persisted state
//   v   = report battery voltage
//   s N = set sip threshold to N grams       (e.g. s20)
//   i N = set tilt threshold to N m/s^2      (e.g. i3.5)
//   b N = set LED brightness, 0-255          (e.g. b30)
//   0   = stop tracker
// ============================================================

// ---------------- BLE SETTINGS ----------------
#define SERVICE_UUID "6E400001-B5A3-F393-E0A9-E50E24DCCA9E"
#define CHARACTERISTIC_UUID_RX "6E400002-B5A3-F393-E0A9-E50E24DCCA9E"
#define CHARACTERISTIC_UUID_TX "6E400003-B5A3-F393-E0A9-E50E24DCCA9E"

String bleDeviceName;
BLECharacteristic *txCharacteristic = nullptr;
bool deviceConnected = false;
bool oldDeviceConnected = false;
String pendingBleCommand = "";
bool bleCommandReady = false;

// ---------------- PINS ----------------
const int HX711_DOUT_PIN = D2;
const int HX711_SCK_PIN = D3;
const int MPU_SDA_PIN = D4;
const int MPU_SCL_PIN = D5;
// D1 (GPIO3) on XIAO ESP32-C3 is ADC1_CH3. Wire BAT+ through a 100k/100k
// divider into D1 to enable real battery readings. Without the divider the
// reading will be garbage but the firmware still compiles and runs.
const int VBAT_ADC_PIN = D1;

#define NEO_PIN D0
#define NEO_COUNT 17

// ---------------- TUNING DEFAULTS (overridden from NVS) ----------------
const float DEFAULT_SIP_THRESHOLD_G = 15.0;
const float DEFAULT_TILT_THRESHOLD_MS2 = 4.0;
const uint8_t DEFAULT_LED_BRIGHTNESS = 30; // V4: 60 -> 30 for brownout headroom
const float RED_WEIGHT_THRESHOLD_G = 15.0;
const int READ_SAMPLES = 10;

// ---------------- POWER MANAGEMENT ----------------
const unsigned long ACTIVE_POLL_INTERVAL_MS = 500;
const unsigned long IDLE_POLL_INTERVAL_MS = 4000;
const unsigned long IDLE_TIMEOUT_MS = 30000; // 30s no motion -> idle
const float WEIGHT_MOTION_DELTA_G = 2.0;     // weight change that counts as motion

// ---------------- BATTERY ----------------
// Assumes BAT+ -> 100k -> ADC -> 100k -> GND so the ADC sees Vbat / 2.
const float VBAT_DIVIDER_RATIO = 2.0;
const float VBAT_FULL = 4.20;
const float VBAT_EMPTY = 3.30;
const unsigned long BATTERY_REPORT_INTERVAL_MS = 30000;

// ---------------- OBJECTS ----------------
HX711 scale;
Preferences prefs;
Adafruit_MPU6050 mpu;
Adafruit_NeoPixel strip(NEO_COUNT, NEO_PIN, NEO_GRB + NEO_KHZ800);

// ---------------- STATE ----------------
float calibrationFactor = 1.0;
long zeroOffset = 0;
bool isCalibrated = false;
bool hxReady = false;
bool mpuReady = false;

// Runtime-configurable (saved to NVS)
float sipThresholdG = DEFAULT_SIP_THRESHOLD_G;
float tiltThresholdMs2 = DEFAULT_TILT_THRESHOLD_MS2;
uint8_t ledBrightness = DEFAULT_LED_BRIGHTNESS;

// Persistent totals
uint32_t lifetimeSipCount = 0;
float lifetimeTotalG = 0.0;

unsigned long lastBlinkTime = 0;
bool blinkState = false;

enum RunMode
{
    MODE_IDLE_MENU,
    MODE_TEST
};
RunMode currentMode = MODE_IDLE_MENU;

enum PowerState
{
    POWER_ACTIVE,
    POWER_LOW
};
PowerState powerState = POWER_ACTIVE;
unsigned long lastMotionMs = 0;
unsigned long lastModeUpdate = 0;
unsigned long lastBatteryReportMs = 0;

float previousWeight = 0.0;
float sessionDrankG = 0.0;
float mostRecentSipG = 0.0;
int sessionSipCount = 0;

bool wasTilted = false;
float weightBeforeTiltG = 0.0;

// ---- ORIENTATION CALIBRATION ----
// The MPU-6050 PCB can be mounted in any of six orientations inside the
// bottle (upside down, sideways, rotated). Gravity isn't always on +Z.
// On boot — and on demand via the 'o' command — we sample the accel
// vector while the bottle is upright and figure out which axis is "up".
// Tilt is then computed as the magnitude of the horizontal-plane axes
// (the two non-"up" axes), so it works regardless of mount orientation.
enum GravityAxis
{
    GAXIS_X,
    GAXIS_Y,
    GAXIS_Z
};
GravityAxis gravityAxis = GAXIS_Z;
int8_t gravitySign = 1; // +1 means gravity reads positive on the up-axis (MPU upright)
bool orientCalibrated = false;

// ---- STRAW-SIP DETECTION ----
// Tilt-based detection misses drinks through a straw (the bottle barely
// moves). Watch for a sustained weight drop while the bottle is upright:
// if weight has been monotonically decreasing for >= STRAW_WINDOW_MS and
// the total drop is >= sipThresholdG, count it as a sip.
bool inStrawWindow = false;
float strawStartWeightG = 0.0;
unsigned long strawWindowStartMs = 0;
const unsigned long STRAW_WINDOW_MS = 3000; // 3s of monotonic drop
const float STRAW_DROP_GATE_G = 1.5;        // ignore sub-1.5g noise

// ---- REFILL DETECTION ----
// If weight just jumped UP by more than REFILL_RISE_G in one polling
// tick, the user just added water. Pause sip detection so partial
// sloshing or post-refill tilts don't get mis-counted. Resume early
// once weight has been stable (delta < REFILL_STABLE_DELTA_G) for
// REFILL_STABLE_POLLS consecutive ticks, OR after REFILL_PAUSE_MS as
// a backstop. Fully firmware-side — the app/UX never knows.
bool refillPaused = false;
unsigned long refillPauseUntilMs = 0;
int refillStableCount = 0;
const float REFILL_RISE_G = 5.0;             // weight jump that triggers pause
const unsigned long REFILL_PAUSE_MS = 30000; // hard timeout (30s)
const float REFILL_STABLE_DELTA_G = 1.0;     // |delta| under this counts as "stable"
const int REFILL_STABLE_POLLS = 3;           // consecutive stable ticks → early resume

// ============================================================
// FORWARD DECLARATIONS
// ============================================================
String makeBleName();
void setupBLE();
void showMenu();
void handleCommand(String cmd, bool fromBLE);

void startTestMode();
void updateTestMode();
void stopMode();

void showTestLEDs(bool isTilted, bool isEmpty);
void rampLedsOnBoot();
void flashConnected();

void enterLowPower();
void exitLowPower();

void doRetare();
void clearLifetimeStats();
void calibrateOrientation(bool quiet);
float tiltMagnitude(const sensors_event_t &a);
void reportBatteryVoltage();
float readBatteryVoltage();
int batteryPercent(float voltage);

void sendLine(String msg);
float gramsToOunces(float grams);

void runCalibration();
void loadCalibration();
void saveCalibration();
void saveZeroOffset();
void loadSettings();
void saveSettings();
void loadTotals();
void saveTotals();

// ============================================================
// BLE CALLBACKS
// ============================================================
class MyServerCallbacks : public BLEServerCallbacks
{
    void onConnect(BLEServer *pServer) override { deviceConnected = true; }
    void onDisconnect(BLEServer *pServer) override { deviceConnected = false; }
};

class MyRxCallbacks : public BLECharacteristicCallbacks
{
    void onWrite(BLECharacteristic *pCharacteristic) override
    {
        String value = String(pCharacteristic->getValue().c_str());
        value.trim();

        if (value.length() > 0)
        {
            pendingBleCommand = value;
            bleCommandReady = true;
        }
    }
};

// ============================================================
// SETUP
// ============================================================
void setup()
{
    Serial.begin(115200);
    delay(500);

    // Load settings first so the brightness used by rampLedsOnBoot is correct.
    loadSettings();
    loadTotals();

    strip.begin();
    strip.setBrightness(ledBrightness);
    strip.clear();
    strip.show();
    rampLedsOnBoot();

    analogReadResolution(12);

    scale.begin(HX711_DOUT_PIN, HX711_SCK_PIN);
    hxReady = scale.wait_ready_timeout(2000);

    Wire.begin(MPU_SDA_PIN, MPU_SCL_PIN);
    mpuReady = mpu.begin();

    if (mpuReady)
    {
        mpu.setAccelerometerRange(MPU6050_RANGE_8_G);
        mpu.setFilterBandwidth(MPU6050_BAND_21_HZ);

        // Configure motion-detect on the MPU itself. The status latches even
        // when the INT pin isn't wired, so motion-wake works in software too.
        mpu.setMotionDetectionThreshold(1);
        mpu.setMotionDetectionDuration(20);
        mpu.setInterruptPinLatch(true);
        mpu.setInterruptPinPolarity(true);
        mpu.setMotionInterrupt(true);
    }

    bleDeviceName = makeBleName();
    setupBLE();
    loadCalibration();

    // Auto-detect MPU mount orientation from the resting gravity vector.
    // Quiet mode = no BLE chatter (no one's connected yet anyway).
    if (mpuReady)
        calibrateOrientation(true);

    lastMotionMs = millis();

    Serial.println();
    Serial.println("SipSync V4 started.");
    Serial.println("BLE advertising as: " + bleDeviceName);
    Serial.print("HX711 ready: ");
    Serial.println(hxReady ? "YES" : "NO");
    Serial.print("MPU ready: ");
    Serial.println(mpuReady ? "YES" : "NO");
    Serial.print("Calibrated: ");
    Serial.println(isCalibrated ? "YES" : "NO");
    Serial.print("Lifetime sips: ");
    Serial.println(lifetimeSipCount);
    Serial.print("Lifetime grams: ");
    Serial.println(lifetimeTotalG, 1);

    showMenu();
}

// ============================================================
// LOOP
// ============================================================
void loop()
{
    if (!deviceConnected && oldDeviceConnected)
    {
        // App just disconnected. If the disconnect was abrupt (out of range,
        // app killed, BT toggled off), the firmware never received the '0'
        // command, so currentMode would stay in MODE_TEST and showTestLEDs()
        // would keep flipping blue/green forever. Force-stop locally so the
        // bottle goes back to "dark while advertising."
        if (currentMode == MODE_TEST)
            stopMode();
        delay(500);
        BLEDevice::startAdvertising();
        oldDeviceConnected = deviceConnected;
    }

    if (deviceConnected && !oldDeviceConnected)
    {
        oldDeviceConnected = deviceConnected;
        flashConnected();
        showMenu();
    }

    if (Serial.available())
    {
        String cmd = Serial.readStringUntil('\n');
        cmd.trim();
        if (cmd.length() > 0)
        {
            handleCommand(cmd, false);
        }
    }

    if (bleCommandReady)
    {
        handleCommand(pendingBleCommand, true);
        bleCommandReady = false;
        pendingBleCommand = "";
    }

    // ----------------------------------------------------------------
    // Fast motion-wake.
    // The MPU's motion interrupt status latches in hardware. We poll it
    // every loop tick (~20ms) — that's a single cheap I2C read, way
    // cheaper than the HX711 weighing inside updateTestMode(). The
    // moment the user picks up the bottle, we exit low power and the
    // next updateTestMode() runs at the 500ms ACTIVE interval — so a
    // 2-3s sip cycle is never missed because we were asleep on a 4s
    // idle poll.
    // ----------------------------------------------------------------
    if (mpuReady && powerState == POWER_LOW && currentMode == MODE_TEST)
    {
        if (mpu.getMotionInterruptStatus())
        {
            lastMotionMs = millis();
            exitLowPower();
        }
    }

    if (currentMode == MODE_TEST)
    {
        updateTestMode();
    }

    // delay() on Arduino-ESP32 yields to FreeRTOS, which lets the BLE modem
    // sleep automatically between connection events.
    delay(20);
}

// ============================================================
// MENU + COMMANDS
// ============================================================
void showMenu()
{
    sendLine("---- SipSync V4 Menu ----");
    sendLine(bleDeviceName);
    sendLine("1   = Calibrate (USB only)");
    sendLine("t   = Tracker mode");
    sendLine("r   = Re-tare load cell");
    sendLine("c   = Clear lifetime stats");
    sendLine("o   = Re-calibrate MPU orientation");
    sendLine("p   = Print persisted state");
    sendLine("v   = Battery voltage");
    sendLine("s N = Set sip threshold (g)");
    sendLine("i N = Set tilt threshold (m/s2)");
    sendLine("b N = Set brightness 0-255");
    sendLine("0   = Stop tracker");
    sendLine("m   = Menu");
}

void handleCommand(String cmd, bool fromBLE)
{
    cmd.trim();
    if (cmd.length() == 0)
        return;

    String rest = cmd.substring(1);
    rest.trim();

    String lower = cmd;
    lower.toLowerCase();
    char c = lower.charAt(0);

    switch (c)
    {
    case 'm':
        showMenu();
        break;

    case '0':
        stopMode();
        break;

    case '1':
        if (!fromBLE)
            runCalibration();
        else
            sendLine("Calibration is USB Serial only.");
        break;

    case 't':
        startTestMode();
        break;

    case 'r':
        doRetare();
        break;

    case 'c':
        clearLifetimeStats();
        break;

    case 'o':
        // Re-run orientation calibration. Make sure the bottle is upright
        // and still when sending this command.
        if (!mpuReady)
        {
            sendLine("MPU not ready.");
        }
        else
        {
            sendLine("Re-calibrating orientation. Keep bottle upright...");
            calibrateOrientation(false);
        }
        break;

    case 'p':
        sendLine("Lifetime sips: " + String(lifetimeSipCount));
        sendLine("Lifetime grams: " + String(lifetimeTotalG, 1));
        sendLine("Lifetime oz: " + String(gramsToOunces(lifetimeTotalG), 2));
        sendLine("Sip threshold: " + String(sipThresholdG, 1) + " g");
        sendLine("Tilt threshold: " + String(tiltThresholdMs2, 2) + " m/s^2");
        sendLine("Brightness: " + String(ledBrightness));
        sendLine("Cal factor: " + String(calibrationFactor, 4));
        sendLine("Zero offset: " + String(zeroOffset));
        sendLine("Power state: " + String(powerState == POWER_LOW ? "LOW" : "ACTIVE"));
        sendLine("Refill paused: " + String(refillPaused ? "YES" : "NO"));
        {
            const char *axisName = gravityAxis == GAXIS_X   ? "X"
                                   : gravityAxis == GAXIS_Y ? "Y"
                                                            : "Z";
            sendLine(String("Up axis: ") + (gravitySign > 0 ? "+" : "-") + axisName +
                     (orientCalibrated ? " (calibrated)" : " (default)"));
        }
        break;

    case 'v':
        reportBatteryVoltage();
        break;

    case 's':
    {
        float v = rest.toFloat();
        if (v > 0 && v < 1000)
        {
            sipThresholdG = v;
            saveSettings();
            sendLine("Sip threshold = " + String(sipThresholdG, 1) + " g");
        }
        else
        {
            sendLine("Bad value. Try s15");
        }
        break;
    }

    case 'i':
    {
        float v = rest.toFloat();
        if (v > 0 && v < 20)
        {
            tiltThresholdMs2 = v;
            saveSettings();
            sendLine("Tilt threshold = " + String(tiltThresholdMs2, 2) + " m/s^2");
        }
        else
        {
            sendLine("Bad value. Try i4.0");
        }
        break;
    }

    case 'b':
    {
        int v = rest.toInt();
        if (v >= 0 && v <= 255)
        {
            ledBrightness = (uint8_t)v;
            strip.setBrightness(ledBrightness);
            strip.show();
            saveSettings();
            sendLine("Brightness = " + String(ledBrightness));
        }
        else
        {
            sendLine("Bad value. Try b30 (0-255)");
        }
        break;
    }

    default:
        sendLine("Unknown command.");
        showMenu();
        break;
    }
}

// ============================================================
// TRACKER MODE
// ============================================================
void startTestMode()
{
    if (!hxReady || !isCalibrated)
    {
        sendLine("HX711 setup/calibration error.");
        sendLine("Run calibration first using USB command 1.");
        return;
    }

    if (!mpuReady)
    {
        sendLine("MPU6050 not ready.");
        return;
    }

    scale.set_scale(calibrationFactor);
    scale.set_offset(zeroOffset);

    float currentWeight = scale.get_units(READ_SAMPLES);

    previousWeight = currentWeight;
    weightBeforeTiltG = currentWeight;
    sessionSipCount = 0;
    sessionDrankG = 0.0;
    mostRecentSipG = 0.0;
    wasTilted = false;

    currentMode = MODE_TEST;
    lastModeUpdate = 0;
    lastMotionMs = millis();
    exitLowPower();

    sendLine("Tracker Mode ON");
    sendLine("Sip = tilt then untilt with drop >= " + String(sipThresholdG, 1) + " g.");
    sendLine("Send 0 to stop.");
}

void updateTestMode()
{
    unsigned long interval = (powerState == POWER_LOW) ? IDLE_POLL_INTERVAL_MS
                                                       : ACTIVE_POLL_INTERVAL_MS;
    if (millis() - lastModeUpdate < interval)
        return;
    lastModeUpdate = millis();

    sensors_event_t a, g, temp;
    mpu.getEvent(&a, &g, &temp);

    float currentWeightG = scale.get_units(READ_SAMPLES);
    float currentWeightOz = gramsToOunces(currentWeightG);

    // Orientation-agnostic tilt detection: magnitude of the two non-"up"
    // axes. When upright, both read ~0 regardless of which MPU axis is up.
    // When the bottle tips, gravity bleeds out of the up-axis into them.
    bool isTilted = tiltMagnitude(a) > tiltThresholdMs2;
    bool isEmpty = currentWeightG < RED_WEIGHT_THRESHOLD_G;

    // Motion-wake: any tilt or measurable weight change resets the idle timer.
    bool motionDetected = isTilted ||
                          fabs(currentWeightG - previousWeight) > WEIGHT_MOTION_DELTA_G;

    if (motionDetected)
    {
        lastMotionMs = millis();
        if (powerState == POWER_LOW)
            exitLowPower();
    }
    else if (powerState == POWER_ACTIVE &&
             millis() - lastMotionMs > IDLE_TIMEOUT_MS)
    {
        enterLowPower();
    }

    if (powerState == POWER_ACTIVE)
    {
        showTestLEDs(isTilted, isEmpty);
    }

    // ------------------------------------------------------------
    // REFILL DETECTION: a sudden positive weight jump means the
    // user just added water. Pause sip detection so sloshing /
    // tilting during the refill doesn't trigger false sips.
    // ------------------------------------------------------------
    float weightDeltaSignedG = currentWeightG - previousWeight;
    if (!refillPaused)
    {
        if (weightDeltaSignedG > REFILL_RISE_G)
        {
            refillPaused = true;
            refillPauseUntilMs = millis() + REFILL_PAUSE_MS;
            refillStableCount = 0;
            // Cancel any in-flight detection state — partial drinks
            // before the refill shouldn't bleed into the post-refill
            // baseline.
            inStrawWindow = false;
            wasTilted = false;
            sendLine("Refill detected (+" + String(weightDeltaSignedG, 1) + " g). Detection paused.");
        }
    }
    else
    {
        // Early-resume: weight stable for REFILL_STABLE_POLLS consecutive ticks
        // means the user is done pouring. Backstop timeout is the hard limit.
        if (fabs(weightDeltaSignedG) < REFILL_STABLE_DELTA_G)
        {
            refillStableCount++;
        }
        else
        {
            refillStableCount = 0;
        }
        if (refillStableCount >= REFILL_STABLE_POLLS || millis() >= refillPauseUntilMs)
        {
            refillPaused = false;
            wasTilted = false;
            inStrawWindow = false;
            sendLine("Refill pause ended. Resuming detection.");
        }
    }

    // ------------------------------------------------------------
    // SIP LOGIC (skipped during refill pause):
    // 1. When bottle first tilts, save starting weight.
    // 2. When bottle returns to not tilted, compare weight drop.
    // 3. If drop is >= sipThresholdG, count one sip.
    // ------------------------------------------------------------
    if (!refillPaused && isTilted && !wasTilted)
    {
        weightBeforeTiltG = currentWeightG;
        wasTilted = true;
        sendLine("Tilt started. Start weight: " + String(weightBeforeTiltG, 1) + " g");
    }

    if (!isTilted && wasTilted)
    {
        float weightAfterTiltG = currentWeightG;
        float sipDeltaG = weightBeforeTiltG - weightAfterTiltG;
        wasTilted = false;

        if (sipDeltaG >= sipThresholdG)
        {
            sessionSipCount++;
            mostRecentSipG = sipDeltaG;
            sessionDrankG += sipDeltaG;

            lifetimeSipCount++;
            lifetimeTotalG += sipDeltaG;
            saveTotals();

            // Tilt-sip just fired — cancel any open straw window so the same
            // drink isn't double-counted by the upright detector below.
            inStrawWindow = false;

            // "Most recent sip:" line is what the MyFitnessTech app keys
            // off after SIP DETECTED to auto-log a water entry. Don't rename it.
            sendLine("SIP DETECTED");
            sendLine("Most recent sip: " + String(gramsToOunces(mostRecentSipG), 2) + " oz");
            sendLine("Most recent sip grams: " + String(mostRecentSipG, 1) + " g");
            sendLine("Session total: " + String(gramsToOunces(sessionDrankG), 2) + " oz");
            sendLine("Lifetime sips: " + String(lifetimeSipCount));
            sendLine("Lifetime total: " + String(gramsToOunces(lifetimeTotalG), 2) + " oz");
        }
        else
        {
            sendLine("Tilt ended, sip too small: " + String(sipDeltaG, 1) + " g");
        }
    }

    // ------------------------------------------------------------
    // STRAW-SIP DETECTION (only while NOT tilted AND not refilling).
    // 1. Weight drops below recent baseline by STRAW_DROP_GATE_G → open window
    // 2. Window stays open as long as weight is non-increasing
    // 3. On weight rise (refill / pickup) or expiry, evaluate total drop
    // 4. If >= sipThresholdG AND window held for >= STRAW_WINDOW_MS, log sip
    // ------------------------------------------------------------
    if (!refillPaused && !isTilted)
    {
        float deltaSincePrev = previousWeight - currentWeightG; // >0 = lost weight
        if (!inStrawWindow)
        {
            if (deltaSincePrev > STRAW_DROP_GATE_G)
            {
                inStrawWindow = true;
                strawStartWeightG = previousWeight;
                strawWindowStartMs = millis();
            }
        }
        else
        {
            bool weightRose = deltaSincePrev < -STRAW_DROP_GATE_G;
            float totalDrop = strawStartWeightG - currentWeightG;
            unsigned long elapsed = millis() - strawWindowStartMs;

            // Close the window if weight starts going up, or if it's been
            // open way longer than the minimum window (no further drops).
            if (weightRose || elapsed > STRAW_WINDOW_MS * 3)
            {
                if (elapsed >= STRAW_WINDOW_MS && totalDrop >= sipThresholdG)
                {
                    sessionSipCount++;
                    mostRecentSipG = totalDrop;
                    sessionDrankG += totalDrop;

                    lifetimeSipCount++;
                    lifetimeTotalG += totalDrop;
                    saveTotals();

                    sendLine("SIP DETECTED");
                    sendLine("Most recent sip: " + String(gramsToOunces(totalDrop), 2) + " oz");
                    sendLine("Most recent sip grams: " + String(totalDrop, 1) + " g");
                    sendLine("(straw)");
                    sendLine("Session total: " + String(gramsToOunces(sessionDrankG), 2) + " oz");
                    sendLine("Lifetime sips: " + String(lifetimeSipCount));
                    sendLine("Lifetime total: " + String(gramsToOunces(lifetimeTotalG), 2) + " oz");
                }
                inStrawWindow = false;
            }
        }
    }
    else
    {
        // Bottle tilted → straw detection doesn't apply, drop any open window.
        inStrawWindow = false;
    }

    float displayWeight = currentWeightG;
    if (displayWeight < 0.0)
    {
        displayWeight = 0.0;
    }

    // Telemetry line MUST stay byte-compatible with V3 so the MyFitnessTech
    // app regex (Last sip: / Total drank:) keeps parsing it. Power state is
    // emitted on its own line so the regex's end-anchor still matches.
    String msg = "Weight: " + String(displayWeight, 1) +
                 " g / " + String(gramsToOunces(displayWeight), 2) +
                 " oz | Sips: " + String(sessionSipCount) +
                 " | Last sip: " + String(gramsToOunces(mostRecentSipG), 2) +
                 " oz | Total drank: " + String(gramsToOunces(sessionDrankG), 2) +
                 " oz | Tilted: " + String(isTilted ? "YES" : "NO");
    sendLine(msg);
    sendLine("Pwr: " + String(powerState == POWER_LOW ? "LOW" : "ACTIVE"));

    if (millis() - lastBatteryReportMs > BATTERY_REPORT_INTERVAL_MS)
    {
        lastBatteryReportMs = millis();
        float vbat = readBatteryVoltage();
        sendLine("Battery: " + String(vbat, 2) + " V (" + String(batteryPercent(vbat)) + "%)");
    }

    previousWeight = currentWeightG;
}

void stopMode()
{
    currentMode = MODE_IDLE_MENU;
    strip.clear();
    strip.show();
    sendLine("Stopped.");
}

// ============================================================
// POWER MANAGEMENT
// ============================================================
void enterLowPower()
{
    if (powerState == POWER_LOW)
        return;
    powerState = POWER_LOW;
    strip.clear();
    strip.show();
    sendLine("Idle: low power.");
}

void exitLowPower()
{
    if (powerState == POWER_ACTIVE)
        return;
    powerState = POWER_ACTIVE;
    strip.setBrightness(ledBrightness);
    sendLine("Active.");
}

// ============================================================
// LED LOGIC
// ============================================================
void showTestLEDs(bool isTilted, bool isEmpty)
{
    unsigned long now = millis();

    if (isEmpty)
    {
        for (int i = 0; i < NEO_COUNT; i++)
        {
            strip.setPixelColor(i, strip.Color(255, 0, 0));
        }
    }
    else if (isTilted)
    {
        if (now - lastBlinkTime >= 250)
        {
            lastBlinkTime = now;
            blinkState = !blinkState;
        }
        for (int i = 0; i < NEO_COUNT; i++)
        {
            strip.setPixelColor(i, blinkState ? strip.Color(0, 255, 0) : 0);
        }
    }
    else
    {
        for (int i = 0; i < NEO_COUNT; i++)
        {
            strip.setPixelColor(i, strip.Color(0, 0, 60));
        }
    }

    strip.show();
}

void rampLedsOnBoot()
{
    // Brownout-friendly ramp: climb from 0 to target brightness with
    // dim white so the regulator isn't slammed by 17 LEDs at once.
    for (uint8_t b = 0; b <= ledBrightness; b += 5)
    {
        strip.setBrightness(b);
        for (int i = 0; i < NEO_COUNT; i++)
        {
            strip.setPixelColor(i, strip.Color(20, 20, 20));
        }
        strip.show();
        delay(15);
    }
    strip.clear();
    strip.setBrightness(ledBrightness);
    strip.show();
}

// Single bright green flash all 17 LEDs as a handshake confirmation
// when the app connects. Bottle is otherwise dark while advertising,
// so this is the "I see you" signal. ~300ms total then back to black;
// the app sends 't' right after connect, which kicks tracker mode and
// hands the LEDs over to showTestLEDs() for water-state colors.
void flashConnected()
{
    strip.setBrightness(ledBrightness);
    for (int i = 0; i < NEO_COUNT; i++)
    {
        strip.setPixelColor(i, strip.Color(0, 255, 0));
    }
    strip.show();
    delay(300);
    strip.clear();
    strip.show();
}

// ============================================================
// BLE SETUP
// ============================================================
String makeBleName()
{
    uint64_t mac = ESP.getEfuseMac();
    char name[20];
    snprintf(name, sizeof(name), "SipSync-%04X", (uint16_t)(mac & 0xFFFF));
    return String(name);
}

void setupBLE()
{
    BLEDevice::init(bleDeviceName.c_str());

    BLEServer *pServer = BLEDevice::createServer();
    pServer->setCallbacks(new MyServerCallbacks());

    BLEService *pService = pServer->createService(SERVICE_UUID);

    txCharacteristic = pService->createCharacteristic(
        CHARACTERISTIC_UUID_TX,
        BLECharacteristic::PROPERTY_NOTIFY);
    txCharacteristic->addDescriptor(new BLE2902());

    BLECharacteristic *rxChar = pService->createCharacteristic(
        CHARACTERISTIC_UUID_RX,
        BLECharacteristic::PROPERTY_WRITE);
    rxChar->setCallbacks(new MyRxCallbacks());

    pService->start();
    BLEDevice::startAdvertising();

    Serial.println("BLE advertising as: " + bleDeviceName);
}

// ============================================================
// RE-TARE / STATS
// ============================================================
void doRetare()
{
    if (!hxReady)
    {
        sendLine("HX711 not ready.");
        return;
    }
    if (!isCalibrated)
    {
        sendLine("Not calibrated. Run 1 over USB first.");
        return;
    }

    scale.set_scale(calibrationFactor);
    scale.tare(20);
    zeroOffset = scale.get_offset();
    saveZeroOffset();

    sendLine("Tared. New zero offset: " + String(zeroOffset));
}

void clearLifetimeStats()
{
    lifetimeSipCount = 0;
    lifetimeTotalG = 0.0;
    saveTotals();
    sendLine("Lifetime stats cleared.");
}

// ============================================================
// ORIENTATION CALIBRATION
// ============================================================
// Sample the resting gravity vector for ~500ms. The axis with the
// largest magnitude is "up"; the sign tells us whether the MPU PCB is
// mounted upside-down. Stored in RAM only — recomputed on every boot.
void calibrateOrientation(bool quiet)
{
    const int samples = 20;
    const int perSampleMs = 25;
    float sumX = 0.0, sumY = 0.0, sumZ = 0.0;

    for (int i = 0; i < samples; i++)
    {
        sensors_event_t a, g, temp;
        mpu.getEvent(&a, &g, &temp);
        sumX += a.acceleration.x;
        sumY += a.acceleration.y;
        sumZ += a.acceleration.z;
        delay(perSampleMs);
    }

    float avgX = sumX / samples;
    float avgY = sumY / samples;
    float avgZ = sumZ / samples;
    float absX = fabs(avgX), absY = fabs(avgY), absZ = fabs(avgZ);

    if (absZ >= absX && absZ >= absY)
    {
        gravityAxis = GAXIS_Z;
        gravitySign = (avgZ >= 0) ? 1 : -1;
    }
    else if (absY >= absX)
    {
        gravityAxis = GAXIS_Y;
        gravitySign = (avgY >= 0) ? 1 : -1;
    }
    else
    {
        gravityAxis = GAXIS_X;
        gravitySign = (avgX >= 0) ? 1 : -1;
    }
    orientCalibrated = true;

    if (!quiet)
    {
        const char *axisName = gravityAxis == GAXIS_X   ? "X"
                               : gravityAxis == GAXIS_Y ? "Y"
                                                        : "Z";
        sendLine(String("Orientation set: up = ") +
                 (gravitySign > 0 ? "+" : "-") + axisName +
                 " | resting g = (" + String(avgX, 2) +
                 ", " + String(avgY, 2) +
                 ", " + String(avgZ, 2) + ") m/s^2");
    }
}

// Magnitude of the acceleration component in the horizontal plane
// (the two axes that are NOT the calibrated "up" axis). When upright,
// gravity sits entirely on the up-axis and this reads ~0. When the
// bottle tips, gravity bleeds into the other two axes and this grows.
float tiltMagnitude(const sensors_event_t &a)
{
    float ax = a.acceleration.x;
    float ay = a.acceleration.y;
    float az = a.acceleration.z;
    float h1 = 0.0, h2 = 0.0;
    switch (gravityAxis)
    {
    case GAXIS_X:
        h1 = ay;
        h2 = az;
        break;
    case GAXIS_Y:
        h1 = ax;
        h2 = az;
        break;
    case GAXIS_Z:
        h1 = ax;
        h2 = ay;
        break;
    }
    return sqrtf(h1 * h1 + h2 * h2);
}

// ============================================================
// BATTERY
// ============================================================
float readBatteryVoltage()
{
    int raw = analogRead(VBAT_ADC_PIN);
    // ESP32-C3 ADC: 12-bit, ~3.3 V full scale at default attenuation
    float v = (raw / 4095.0f) * 3.3f * VBAT_DIVIDER_RATIO;
    return v;
}

int batteryPercent(float voltage)
{
    float pct = (voltage - VBAT_EMPTY) / (VBAT_FULL - VBAT_EMPTY) * 100.0f;
    if (pct < 0)
        pct = 0;
    if (pct > 100)
        pct = 100;
    return (int)pct;
}

void reportBatteryVoltage()
{
    float v = readBatteryVoltage();
    sendLine("Battery: " + String(v, 2) + " V (" + String(batteryPercent(v)) + "%)");
    sendLine("(Requires 100k/100k divider into D1.)");
}

// ============================================================
// HELPERS
// ============================================================
void sendLine(String msg)
{
    Serial.println(msg);
    if (deviceConnected && txCharacteristic)
    {
        txCharacteristic->setValue(msg.c_str());
        txCharacteristic->notify();
    }
}

float gramsToOunces(float grams) { return grams * 0.035274f; }

// ============================================================
// CALIBRATION
// ============================================================
void runCalibration()
{
    if (!hxReady)
    {
        Serial.println("HX711 not ready.");
        return;
    }

    Serial.println();
    Serial.println("=== Calibration started ===");
    Serial.println("Remove all weight from the load cell.");
    Serial.println("Send any key when ready.");

    while (!Serial.available())
        delay(50);
    while (Serial.available())
        Serial.read();

    scale.set_scale(1.0);
    scale.tare(20);
    zeroOffset = scale.get_offset();

    Serial.print("Zero offset: ");
    Serial.println(zeroOffset);

    Serial.println("Place a known weight on the load cell.");
    Serial.println("Type the weight in grams and press Enter.");

    while (!Serial.available())
        delay(50);

    String input = Serial.readStringUntil('\n');
    input.trim();
    float knownWeight = input.toFloat();

    if (knownWeight <= 0)
    {
        Serial.println("Invalid weight. Calibration cancelled.");
        return;
    }

    float rawWithWeight = scale.get_units(20);
    if (rawWithWeight == 0)
    {
        Serial.println("Raw reading is 0. Calibration cancelled.");
        return;
    }

    calibrationFactor = rawWithWeight / knownWeight;
    scale.set_scale(calibrationFactor);
    scale.set_offset(zeroOffset);

    isCalibrated = true;
    saveCalibration();

    Serial.println("Calibration saved.");
    Serial.print("Calibration factor: ");
    Serial.println(calibrationFactor, 4);

    showMenu();
}

// ============================================================
// NVS STORAGE
// ============================================================
void loadCalibration()
{
    prefs.begin("sipsync", true);
    isCalibrated = prefs.getBool("calibrated", false);
    if (isCalibrated)
    {
        calibrationFactor = prefs.getFloat("calFactor", 1.0);
        zeroOffset = prefs.getLong("zeroOffset", 0);
        scale.set_scale(calibrationFactor);
        scale.set_offset(zeroOffset);
    }
    prefs.end();
}

void saveCalibration()
{
    prefs.begin("sipsync", false);
    prefs.putBool("calibrated", true);
    prefs.putFloat("calFactor", calibrationFactor);
    prefs.putLong("zeroOffset", zeroOffset);
    prefs.end();
}

void saveZeroOffset()
{
    prefs.begin("sipsync", false);
    prefs.putLong("zeroOffset", zeroOffset);
    prefs.end();
}

void loadSettings()
{
    prefs.begin("sipsync", true);
    sipThresholdG = prefs.getFloat("sipThr", DEFAULT_SIP_THRESHOLD_G);
    tiltThresholdMs2 = prefs.getFloat("tiltThr", DEFAULT_TILT_THRESHOLD_MS2);
    ledBrightness = prefs.getUChar("led", DEFAULT_LED_BRIGHTNESS);
    prefs.end();
}

void saveSettings()
{
    prefs.begin("sipsync", false);
    prefs.putFloat("sipThr", sipThresholdG);
    prefs.putFloat("tiltThr", tiltThresholdMs2);
    prefs.putUChar("led", ledBrightness);
    prefs.end();
}

void loadTotals()
{
    prefs.begin("sipsync", true);
    lifetimeSipCount = prefs.getUInt("lifeCnt", 0);
    lifetimeTotalG = prefs.getFloat("lifeG", 0.0);
    prefs.end();
}

void saveTotals()
{
    prefs.begin("sipsync", false);
    prefs.putUInt("lifeCnt", lifetimeSipCount);
    prefs.putFloat("lifeG", lifetimeTotalG);
    prefs.end();
}
