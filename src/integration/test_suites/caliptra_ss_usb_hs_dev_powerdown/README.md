# High-Speed Device Power-Down Test

**Testcase:** `caliptra_ss_usb_hs_dev_powerdown`

## Overview

Verifies USB HS device power-down and power-up link events detected via DCON_C.

## Operation

VIP host connects at HS and runs SOF. VIP issues VBUS off (power-down). MCU firmware
detects DCON_C events indicating power-down and power-up transitions.

## What Is Verified

- DCON_C fires when VIP removes VBUS (power-down)
- DCON_C fires when VIP restores VBUS (power-up)
- MCU firmware monitors and correctly identifies both transitions

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev_powerdown_sequence.svh` | SVT VIP VBUS power-down/up sequence |
| `caliptra_ss_usb_hs_dev_powerdown_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_dev_powerdown.c` | MCU firmware monitoring DCON_C events |
| `caliptra_ss_usb_hs_dev_powerdown.yml` | Simulation run config |
