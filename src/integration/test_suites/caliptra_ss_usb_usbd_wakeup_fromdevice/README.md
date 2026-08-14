# USB Device-Initiated Wakeup Test

**Testcase:** `caliptra_ss_usb_usbd_wakeup_fromdevice`

## Overview

Verifies device-initiated wakeup using DEVCMDSTAT.DRES_C to assert K-state.

## Operation

VIP host connects, runs SOF, issues SUSPEND. MCU firmware detects DSUS_C, sets DRES_C
to assert K-state resume from the device. VIP detects K and drives RESUME. MCU firmware
confirms resume and logs PASSED.

## What Is Verified

- DEVCMDSTAT.DSUS_C set when device is suspended
- DRES_C assertion drives K-state resume signaling from device
- VIP host detects K-state and completes RESUME
- DEVCMDSTAT.DSUS cleared after resume

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_usbd_wakeup_fromdevice_sequence.svh` | SVT VIP SUSPEND+detect-K+RESUME sequence |
| `caliptra_ss_usb_usbd_wakeup_fromdevice_test.svh` | UVM test class |
| `caliptra_ss_usb_usbd_wakeup_fromdevice.c` | MCU firmware asserting DRES_C |
| `caliptra_ss_usb_usbd_wakeup_fromdevice.yml` | Simulation run config |
