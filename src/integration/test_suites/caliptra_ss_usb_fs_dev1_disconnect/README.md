# USB FS Device Disconnect and Reconnect Test

**Testcase:** `caliptra_ss_usb_fs_dev1_disconnect`

## Overview

Full-speed variant of `caliptra_ss_usb_hs_dev_disconnect`. It verifies the
full USB FS device disconnect and reconnect cycle: enumerate, power the port
off (disconnect), wait, power it back on (reconnect), and re-enumerate.

The disconnect/reconnect behaviour is identical to the HS test - it depends
only on the device controller's VBus debounce / DCON logic, which is
speed-agnostic. The only differences from the HS test are the ones that put
the link into full-speed:

- **Firmware:** boots the USB core with `boot_usb_core_fs()` instead of
  `boot_usb_core()`. `boot_usb_core_fs()` is identical to `boot_usb_core()`
  except it sets `DEVCMDSTAT.PFSC` (bit 21, `USBHSD_DEVCMDSTAT_PFSC_MASK`) to
  suppress the device-side K-chirp so the link negotiates and stays at
  full-speed for the FS-only host VIP.
- **UVM test:** puts the VIP into FS-only mode
  (`host_cfg.local_host_cfg.high_speed_capable = 0`, `host_cfg.speed = FS`,
  `dev_cfg.speed = FS`, `connected_bus_speed = FS`,
  `functionality_support = FS`), re-stamps EP0 CONTROL to FS speed and FS max
  packet size, and widens the FS link stability knobs (`tddis`,
  `tend_to_end_delay_fs`, `tinactivity`, `drive_reset_time`) so the FS link
  survives enumeration in scaledown simulation. Only EP0 is configured - this
  test exercises enumeration and link events only (no EP1/EP2 data traffic).

## Operation

`main()` clears `FORCE_VBUS` (which `boot_usb_core_fs()` sets by default) so
the controller monitors the real VBus pin, since `FORCE_VBUS=1` would make the
DUT ignore VBus removal and disconnect detection would never fire.

| Phase | Action |
|-------|--------|
| 1 | VIP host connects at FS and issues a bus reset. MCU services EP0 SETUP tokens inline until 3 enumeration transfers (`GET_DESCRIPTOR`, `SET_ADDRESS`, `SET_CONFIGURATION`) are handled. |
| 2 | MCU clears any pending `FRAME_INT` and enables then disables `INTEN.FRAME_INT_EN`. The SOF-counting loop is retained only as commented-out reference (matching the HS variant). |
| 3 | VIP host drives a disconnect (VBUS off). MCU polls for `DCON_C` set together with `VBUS_DEBOUNCED` clear (DCON is firmware-controlled and hardware never clears it on VBus removal, so `DCON_C && !DCON` would never fire - the real signal is `DCON_C && !VBUS_DEBOUNCED`). On detection, MCU clears `DCON` (drops FsPullup) then clears `DCON_C` (W1C), and verifies `VBUS_DEBOUNCED` is now clear. |
| 3b | MCU polls for VBus to return (`VBUS_DEBOUNCED` set again), then re-asserts `DCON` so FsPullup goes high and the VIP host can see the device re-attached and drive a fresh bus reset. |
| 4 | VIP host reconnects and issues a second bus reset. MCU re-enumerates the same way as phase 1 (3 more control transfers). |
| 4b | MCU keeps servicing EP0 for a bounded window so the tail of the host-side enumeration (GET_DESCRIPTOR at the new address + SET_CONFIGURATION to USBDC1) is answered and the device never NAKs a SETUP. |
| 5 | MCU re-enables `FRAME_INT_EN` (same as phase 2). Reports `USB FS disconnect test PASSED`. |

## What Is Verified

- FS link enumerates initially and re-enumerates after reconnect
- `VBUS_DEBOUNCED=1` after initial connect and after reconnect
- `VBUS_DEBOUNCED=0` after disconnect (VBUS off)
- `DCON_C` fires on disconnect, detected via `DCON_C && !VBUS_DEBOUNCED`
- `DRES_C` fires on the initial bus reset and again on the bus reset after
  reconnect (enumeration completes both times)
- Firmware explicitly re-asserts `DCON` after VBus returns (phase 3b) so the
  VIP can see the device re-attach; this is a required firmware action, not
  an automatic hardware response
- The link stays at full-speed because `boot_usb_core_fs()` set
  `DEVCMDSTAT.PFSC` to suppress the device K-chirp

## Register Reference

| Register field | Caliptra SS macro |
|---|---|
| Force full-speed (suppress K-chirp) | `USBHSD_DEVCMDSTAT_PFSC_MASK` (bit 21) |
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
| `caliptra_ss_usb_fs_dev1_disconnect_sequence.svh` | SVT VIP sequence: enumerate, disconnect (VBUS off), reconnect (VBUS on), re-enumerate |
| `caliptra_ss_usb_fs_dev1_disconnect_test.svh` | UVM test class: FS-only VIP config + EP0 FS re-stamp + FS link stability knobs |
| `caliptra_ss_usb_fs_dev1_disconnect.c` | MCU firmware: FS bring-up via `boot_usb_core_fs()`, connect/enumerate, disconnect detect, reconnect/re-enumerate |
| `caliptra_ss_usb_fs_dev1_disconnect.yml` | Simulation run config |

> Generated with acc from `caliptra_ss_usb_fs_dev_disconnect` (USBDC1 counterpart). Firmware is retargeted to the USBDC1 aperture by `-DUSB_DEV_SEL=1` and the host sequence brings up hub downstream port 2.
