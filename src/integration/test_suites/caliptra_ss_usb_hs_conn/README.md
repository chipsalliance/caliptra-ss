# High-Speed Device Connection Test

**Testcase:** `caliptra_ss_usb_hs_conn`

## Overview

Verifies HS USB device connection and `DEVCMDSTAT.DCON` assertion on the
hub-composite IP. This is a passive link-observer test: the host sequence
performs the HS chirp/link-up handshake but does not issue any enumeration
control transfers.

## Topology (hub-composite IP)

USBDC0 sits behind the on-chip 2-port USB hub. `boot_usb_core()` programs
USBDC0's EP list/DEVCMDSTAT/DCON and, internally via
`usb_hub_init_and_connect()`, brings the hub up in phase 1 (HUB RAM +
`HUB_EN`). The test's `main()` then calls `usb_hub_connect()` (phase 2,
`HUB_CONNECT`), only after which the host sees the hub on the bus, performs
HS chirp, and begins enumerating its downstream port 0 (USBDC0). Registers
are accessed via the `USB_DEV0_*` bank (base `0x2000_1000`).

## Operation

VIP host performs HS chirp (`high_speed_capable=1`). MCU firmware polls
`USB_DEV0_DEVCMDSTAT.DCON` (servicing any incidental bus reset via
`usb_handle_bus_reset()` along the way). Firmware detects HS connection and
logs PASSED.

## What Is Verified

- Two-phase hub bring-up (`usb_hub_init_and_connect()` + `usb_hub_connect()`)
  results in the host performing HS chirp and connecting
- HS chirp sequence completes at 480 Mbit/s
- `DEVCMDSTAT.DCON` set correctly after HS link-up
- MCU firmware detects HS connection via `USB_DEV0_*` register access

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_conn_sequence.svh` | SVT VIP HS connect sequence (link-up + observation only, no enumeration) |
| `caliptra_ss_usb_hs_conn_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_conn.c` | MCU firmware polling `DEVCMDSTAT.DCON` via `USB_DEV0_*` |
| `caliptra_ss_usb_hs_conn.yml` | Simulation run config |
