# Full-Speed Device-Initiated Remote Wakeup Test

**Testcase:** `caliptra_ss_usb_fs_host_remotewakeup_fromdevice`

## Overview

Verifies device-initiated remote wakeup where MCU firmware asserts K-state via DRES_C.

## Operation

VIP host enumerates the FS device and sends SOF. VIP issues SUSPEND. MCU firmware
detects DSUS_C (device suspended), then asserts DRES_C to drive K-state resume
signaling from the device side. VIP detects the K and issues RESUME. MCU firmware
confirms DSUS cleared.

## What Is Verified

- Device detects suspend via DEVCMDSTAT.DSUS_C
- Firmware asserts DRES_C to drive K-state resume from device side
- VIP host detects K-state and drives RESUME
- DEVCMDSTAT.DSUS cleared after resume

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence.svh` | SVT VIP SUSPEND+RESUME sequence |
| `caliptra_ss_usb_fs_host_remotewakeup_fromdevice_test.svh` | UVM test class |
| `caliptra_ss_usb_fs_host_remotewakeup_fromdevice.c` | MCU firmware asserting DRES_C |
| `caliptra_ss_usb_fs_host_remotewakeup_fromdevice.yml` | Simulation run config |
