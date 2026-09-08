# USB HS Device Disconnect and Reconnect Test

**Testcase:** `caliptra_ss_usb_hs_dev_disconnect`

## Overview

Verifies the full USB HS device disconnect and reconnect cycle. This test
is still on the legacy single-device register model
(`SOC_USBHSD_*`/`SOC_USBHSD_INTEN`/etc, base `0x2000_0000`) - it has not
been ported to the hub-composite IP's `USB_DEV0_*` bank, unlike most other
USB tests in this suite. Do not assume `usb_hub_connect()` semantics apply
here.

## Operation

The test proceeds in phases. `main()` clears `FORCE_VBUS` (which
`boot_usb_core()` sets by default) so the controller monitors the real VBus
pin, since `FORCE_VBUS=1` would make the DUT ignore VBus removal and
disconnect detection would never fire.

| Phase | Action |
|-------|--------|
| 1 | VIP host connects and issues a bus reset. MCU services EP0 SETUP tokens inline until 3 enumeration transfers (`GET_DESCRIPTOR`, `SET_ADDRESS`, `SET_CONFIGURATION`) are handled. |
| 2 | MCU clears any pending `FRAME_INT` and enables `INTEN.FRAME_INT_EN`, then immediately disables it again. The SOF-counting loop that would count 6 `FRAME_INT` events here is present in the source but commented out - no SOF events are actually counted or checked in this phase as currently checked in. |
| 3 | VIP host drives a disconnect (VBUS off). MCU polls for `DCON_C` set together with `VBUS_DEBOUNCED` clear (DCON itself is firmware-controlled and hardware never clears it on VBus removal, so `DCON_C && !DCON` would never fire - the real signal is `DCON_C && !VBUS_DEBOUNCED`). On detection, MCU clears `DCON` (drops FsPullup) then clears `DCON_C` (W1C), and verifies `VBUS_DEBOUNCED` is now clear. |
| 3b | MCU polls for VBus to return (`VBUS_DEBOUNCED` set again), then re-asserts `DCON` so FsPullup goes high and the VIP host can see the device re-attached and drive a fresh bus reset / HS chirp. |
| 4 | VIP host reconnects and issues a second bus reset. MCU re-enumerates the same way as phase 1 (3 more control transfers). |
| 5 | MCU re-enables then re-disables `FRAME_INT_EN` (same as phase 2 - the SOF-counting loop is commented out here too). Reports `USB HS disconnect test PASSED`. |

## What Is Verified

- `VBUS_DEBOUNCED=1` after initial connect and after reconnect
- `VBUS_DEBOUNCED=0` after disconnect (VBUS off)
- `DCON_C` fires on disconnect, detected via `DCON_C && !VBUS_DEBOUNCED`
  (not `DCON_C && !DCON`, since `DCON` is firmware-controlled and hardware
  never clears it on its own)
- `DRES_C` fires on the initial bus reset and again on the bus reset after
  reconnect (enumeration completes both times)
- Firmware explicitly re-asserts `DCON` after VBus returns (phase 3b) so the
  VIP can see the device re-attach; this is a required firmware action, not
  an automatic hardware response

## Not Currently Verified

- The FRAME_INT (SOF) event-counting logic referenced by earlier revisions
  of this file's phases 2 and 5 is present in `caliptra_ss_usb_hs_dev_disconnect.c`
  only as commented-out code. `INTEN.FRAME_INT_EN` is enabled and disabled,
  but no SOF events are actually counted or asserted on in the current
  build.

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
| `caliptra_ss_usb_hs_dev_disconnect_sequence.svh` | SVT VIP sequence: enumerate, disconnect (VBUS off), reconnect (VBUS on), re-enumerate |
| `caliptra_ss_usb_hs_dev_disconnect_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_dev_disconnect.c` | MCU firmware: connect/enumerate, disconnect detect, reconnect/re-enumerate (legacy `SOC_USBHSD_*` register model) |
| `caliptra_ss_usb_hs_dev_disconnect.yml` | Simulation run config |
