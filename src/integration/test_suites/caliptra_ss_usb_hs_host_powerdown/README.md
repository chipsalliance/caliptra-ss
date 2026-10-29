# High-Speed Host Power-Down Test

**Testcase:** `caliptra_ss_usb_hs_host_powerdown`

## Overview

Verifies HS device detects VIP-driven power-down and power-up transitions.

## Operation

VIP host connects at HS, runs SOF, then removes VBUS (power-down).
MCU firmware monitors DEVCMDSTAT.DCON_C for disconnect and reconnect events.

Note: This test was originally a host-mode DUT test. In the Caliptra environment
the DUT is always a USB device; the SVT VIP acts as host.

## What Is Verified

- DCON_C fires when VIP removes VBUS (power-down)
- DCON_C fires when VIP restores VBUS (power-up)
- MCU firmware detects power-down and power-up transitions via DCON_C

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_host_powerdown_sequence.svh` | SVT VIP VBUS removal/restore sequence |
| `caliptra_ss_usb_hs_host_powerdown_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_host_powerdown.c` | MCU firmware monitoring DCON_C |
| `caliptra_ss_usb_hs_host_powerdown.yml` | Simulation run config |
