# High-Speed Host FPR Resume Test

**Testcase:** `caliptra_ss_usb_hs_host_resume`

## Overview

Verifies HS device detects VIP-driven suspend and FPR resume sequence via DSUS_C.

## Operation

VIP host connects at HS, runs SOF, issues SUSPEND, waits for DSUS, then drives FPR
resume. MCU firmware monitors DSUS_C events for the full suspend/resume cycle.

Note: This test was originally a host-mode DUT test. In the Caliptra environment
the DUT is always a USB device; the SVT VIP acts as host.

## What Is Verified

- DEVCMDSTAT.DSUS set when VIP issues HS SUSPEND
- VIP-driven FPR (force port resume) clears DSUS
- MCU firmware detects full suspend/FPR-resume cycle via DSUS_C

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_host_resume_sequence.svh` | SVT VIP SUSPEND+FPR sequence |
| `caliptra_ss_usb_hs_host_resume_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_host_resume.c` | MCU firmware monitoring DSUS_C |
| `caliptra_ss_usb_hs_host_resume.yml` | Simulation run config |
