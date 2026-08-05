# USB Device Host-Initiated Wakeup Test

**Testcase:** `caliptra_ss_usb_usbd_wakeup`

## Overview

Verifies host-initiated suspend and wakeup detection via DEVCMDSTAT DSUS/DSUS_C bits.

## Operation

VIP host connects at FS, runs SOF, then issues SUSPEND. MCU firmware detects DSUS_C
(suspend). VIP host issues RESUME. MCU firmware confirms DSUS cleared and logs PASSED.

## What Is Verified

- DEVCMDSTAT.DSUS_C set when VIP issues SUSPEND
- DEVCMDSTAT.DSUS cleared when VIP drives RESUME
- Full host-initiated suspend/wakeup cycle detected by MCU firmware

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_usbd_wakeup_sequence.svh` | SVT VIP SUSPEND+RESUME sequence |
| `caliptra_ss_usb_usbd_wakeup_test.svh` | UVM test class |
| `caliptra_ss_usb_usbd_wakeup.c` | MCU firmware monitoring DSUS_C/DSUS |
| `caliptra_ss_usb_usbd_wakeup.yml` | Simulation run config |
