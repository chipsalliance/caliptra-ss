# Full-Speed Device Connection Test

**Testcase:** `caliptra_ss_usb_fs_conn`

## Overview

FS counterpart of `caliptra_ss_usb_hs_conn`. Verifies USB device connection and
`DEVCMDSTAT.DCON` assertion on the hub-composite IP at Full Speed
(12 Mbit/s). This is a passive link-observer test: the host sequence performs
the FS link-up handshake but does not issue any enumeration control transfers.

## Topology (hub-composite IP)

USBDC0 sits behind the on-chip 2-port USB hub. `boot_usb_core_fs()` programs
USBDC0's EP list/DEVCMDSTAT/DCON (with `DEVCMDSTAT.PFSC` set to force FS-only
operation) and, internally via `usb_hub_init_and_connect()`, brings the hub up
in phase 1 (HUB RAM + `HUB_EN`). The test's `main()` then calls
`usb_hub_connect()` (phase 2, `HUB_CONNECT`), only after which the host sees
the hub on the bus, links up at FS, and begins enumerating its downstream
port 0 (USBDC0). Registers are accessed via the `USB_DEV0_*` bank
(base `0x2000_1000`).

## Operation

VIP host is configured FS-only (`high_speed_capable=0`) so no HS chirp is
offered and both sides settle at Full Speed. MCU firmware polls
`USB_DEV0_DEVCMDSTAT.DCON` (servicing any incidental bus reset via
`usb_handle_bus_reset()` along the way). Firmware detects the FS connection and
logs PASSED.

## What Is Verified

- Two-phase hub bring-up (`usb_hub_init_and_connect()` + `usb_hub_connect()`)
  results in the host linking up at FS and connecting
- FS link-up completes at 12 Mbit/s (no HS chirp)
- `DEVCMDSTAT.DCON` set correctly after FS link-up
- MCU firmware detects the FS connection via `USB_DEV0_*` register access

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_fs_conn_sequence.svh` | SVT VIP FS connect sequence (link-up + observation only, no enumeration) |
| `caliptra_ss_usb_fs_conn_test.svh` | UVM test class (`high_speed_capable = 0`) |
| `caliptra_ss_usb_fs_conn.c` | MCU firmware polling `DEVCMDSTAT.DCON` via `USB_DEV0_*` |
| `caliptra_ss_usb_fs_conn.yml` | Simulation run config |

> Ported with acc from `caliptra_ss_usb_hs_conn` (FS counterpart).
