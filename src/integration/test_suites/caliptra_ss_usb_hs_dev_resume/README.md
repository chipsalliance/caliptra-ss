# High-Speed Device Host-Driven Resume Test

**Testcase:** `caliptra_ss_usb_hs_dev_resume`

## Overview

Verifies HS device suspend and host-driven resume via DEVCMDSTAT DSUS/DSUS_C.

> **Hub-composite IP migration:** This testcase has been ported to the
> hub-composite USB IP. USBDC0 (the MCU-owned device controller) now sits
> behind an on-chip 2-port USB hub. The firmware brings the hub up
> (`usb_hub_connect()` after `boot_usb_core()`) and accesses the USBDC0
> register bank via `USB_DEV0_*` (base 0x2000_1000) instead of the legacy
> `SOC_USBHSD_*` bank. The UVM host sequence enumerates the HUB at address 1,
> explicitly brings up downstream port 1, then enumerates USBDC0 at address 2
> before the suspend/resume phase. The FPR resume targets USBDC0 (address 2).
> See `claude_md/09_usb_hub_composite_migration.md` for the full checklist.

## Operation

VIP host connects at HS, runs SOF, enumerates the hub and USBDC0 (address 2),
then issues SUSPEND. MCU firmware detects DSUS_C for suspend. VIP host drives
FPR (force port resume). MCU firmware detects DSUS cleared (resumed).


## What Is Verified

- DEVCMDSTAT.DSUS_C set when VIP issues HS SUSPEND
- VIP-driven FPR (force port resume) clears DEVCMDSTAT.DSUS
- MCU firmware detects full suspend/resume cycle via DSUS/DSUS_C

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev_resume_sequence.svh` | SVT VIP SUSPEND+FPR sequence |
| `caliptra_ss_usb_hs_dev_resume_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_dev_resume.c` | MCU firmware monitoring DSUS/DSUS_C |
| `caliptra_ss_usb_hs_dev_resume.yml` | Simulation run config |
