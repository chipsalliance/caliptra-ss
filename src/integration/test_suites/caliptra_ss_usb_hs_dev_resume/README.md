# High-Speed Device Host-Driven Resume Test

**Testcase:** `caliptra_ss_usb_hs_dev_resume`

## Overview

Verifies HS device suspend and host-driven resume via DEVCMDSTAT DSUS/DSUS_C.

## Operation

VIP host connects at HS, runs SOF, issues SUSPEND. MCU firmware detects DSUS_C for
suspend. VIP host drives FPR (force port resume). MCU firmware detects DSUS cleared
(resumed).

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
