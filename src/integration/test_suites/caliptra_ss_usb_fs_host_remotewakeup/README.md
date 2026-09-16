# Full-Speed Host-Initiated Remote Wakeup Test

**Testcase:** `caliptra_ss_usb_fs_host_remotewakeup`

## Overview

Verifies host-initiated FS suspend and resume cycle.

## Operation

VIP host enumerates the FS device and sends SOF. VIP then issues a SUSPEND protocol
service. MCU firmware detects DSUS_C (suspend change). VIP issues a RESUME protocol
service (host-driven). MCU firmware confirms DSUS cleared (device resumed).

## What Is Verified

- Host-initiated suspend: DEVCMDSTAT.DSUS_C set when VIP issues SUSPEND
- Host-driven resume: DEVCMDSTAT.DSUS cleared when VIP drives RESUME
- Full FS suspend/resume cycle completes correctly

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_fs_host_remotewakeup_sequence.svh` | SVT VIP SUSPEND+RESUME sequence |
| `caliptra_ss_usb_fs_host_remotewakeup_test.svh` | UVM test class |
| `caliptra_ss_usb_fs_host_remotewakeup.c` | MCU firmware monitoring DSUS_C/DSUS |
| `caliptra_ss_usb_fs_host_remotewakeup.yml` | Simulation run config |
