# High-Speed Host Remote Wakeup Test

**Testcase:** `caliptra_ss_usb_hs_host_remotewakeup`

## Overview

Verifies HS device suspend and remote wakeup cycle driven by VIP host.

## Operation

VIP host connects at HS, runs SOF, then issues SUSPEND. MCU firmware monitors
DEVCMDSTAT.DSUS_C for suspend and resume events driven by the VIP host.

Note: This test was originally a host-mode DUT test. In the Caliptra environment
the DUT is always a USB device; the SVT VIP acts as host.

## What Is Verified

- DSUS_C set when VIP issues HS SUSPEND
- DSUS cleared when VIP drives remote wakeup RESUME
- MCU firmware monitors full suspend/wakeup cycle via DSUS_C

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_host_remotewakeup_sequence.svh` | SVT VIP SUSPEND+RESUME sequence |
| `caliptra_ss_usb_hs_host_remotewakeup_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_host_remotewakeup.c` | MCU firmware monitoring DSUS_C |
| `caliptra_ss_usb_hs_host_remotewakeup.yml` | Simulation run config |
