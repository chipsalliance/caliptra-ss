# High-Speed Device Remote Wakeup Test

**Testcase:** `caliptra_ss_usb_hs_dev_remote_wakeup`

## Overview

Verifies HS device suspend and remote wakeup signaling events via DSUS_C.

## Operation

VIP host connects at HS, runs SOF, then issues SUSPEND. MCU firmware detects DSUS_C
(suspend change) and monitors DEVCMDSTAT for wakeup events.

## What Is Verified

- DEVCMDSTAT.DSUS_C set when VIP issues HS SUSPEND
- MCU firmware detects suspend event and monitors for wakeup
- HS device remote wakeup signaling path exercised

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev_remote_wakeup_sequence.svh` | SVT VIP HS SUSPEND+wakeup sequence |
| `caliptra_ss_usb_hs_dev_remote_wakeup_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_dev_remote_wakeup.c` | MCU firmware monitoring DSUS_C |
| `caliptra_ss_usb_hs_dev_remote_wakeup.yml` | Simulation run config |
