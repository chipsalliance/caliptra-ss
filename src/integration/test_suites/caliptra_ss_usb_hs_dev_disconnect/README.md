# High-Speed Device Disconnect and Reconnect Test

**Testcase:** `caliptra_ss_usb_hs_dev_disconnect`

## Overview

Verifies HS device disconnect and reconnect cycle detected via DEVCMDSTAT.DCON_C.

## Operation

VIP host connects at HS. MCU firmware waits for DCON=1. VIP host drives a disconnect
(VBUS off) then reconnects (VBUS on). MCU firmware detects DCON_C events for the
disconnect and reconnect and logs PASSED.

## What Is Verified

- DCON_C fires on VIP-driven disconnect (VBUS off)
- DCON_C fires on VIP-driven reconnect (VBUS on)
- MCU firmware correctly handles both disconnect and reconnect events

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev_disconnect_sequence.svh` | SVT VIP VBUS off/on sequence |
| `caliptra_ss_usb_hs_dev_disconnect_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_dev_disconnect.c` | MCU firmware monitoring DCON_C |
| `caliptra_ss_usb_hs_dev_disconnect.yml` | Simulation run config |
