# USB HS Device Disconnect and Reconnect Test

**Testcase:** `caliptra_ss_usb_hs_dev_disconnect`

## Overview

Verifies the full USB HS device disconnect and reconnect cycle on the
Caliptra SS RISC-V MCU environment.

## Operation

The test proceeds in 5 phases:

| Phase | Action |
|-------|--------|
| 1 | VIP host connects and issues a bus reset. MCU waits for DRES_C, then verifies VBUS_DEBOUNCED=1. |
| 2 | MCU enables FRAME_INT and counts 6 SOF events. FRAME_INT is then disabled. |
| 3 | VIP host drives a disconnect (VBUS off). MCU waits for DCON_C with DCON=0, then verifies VBUS_DEBOUNCED=0. |
| 4 | VIP host reconnects (VBUS on) and issues a second bus reset. MCU waits for DRES_C, then verifies VBUS_DEBOUNCED=1 again. |
| 5 | MCU enables FRAME_INT and counts 6 more SOF events. Reports PASSED. |

## What Is Verified

- VBUS_DEBOUNCED=1 after initial connect and after reconnect
- VBUS_DEBOUNCED=0 after disconnect (VBUS off)
- DCON_C fires on disconnect (DCON bit clears)
- DRES_C fires on initial bus reset and on bus reset after reconnect
- 6 SOF (FRAME_INT) events received after each connect/reconnect

## Register Reference

| Register field | Caliptra SS macro |
|---|---|
| VBUS debounced | `USBHSD_DEVCMDSTAT_VBUS_DEBOUNCED_MASK` |
| Connect change | `USBHSD_DEVCMDSTAT_DCON_C_MASK` |
| Connect control | `USBHSD_DEVCMDSTAT_DCON_MASK` |
| Bus reset change | `USBHSD_DEVCMDSTAT_DRES_C_MASK` |
| SOF interrupt (INTSTAT) | `USBHSD_INTSTAT_FRAME_INT_MASK` |
| SOF interrupt enable (INTEN) | `USBHSD_INTEN_FRAME_INT_EN_MASK` |
| Device status interrupt | `USBHSD_INTSTAT_DEV_INT_MASK` |

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev_disconnect_sequence.svh` | SVT VIP sequence: SOF + disconnect (VBUS off) + reconnect (VBUS on) + 6 SOFs each side |
| `caliptra_ss_usb_hs_dev_disconnect_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_dev_disconnect.c` | MCU firmware: 5-phase disconnect/reconnect verification |
| `caliptra_ss_usb_hs_dev_disconnect.yml` | Simulation run config |
