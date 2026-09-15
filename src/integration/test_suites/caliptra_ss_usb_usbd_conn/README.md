# USB Device Connection Detection Test

**Testcase:** `caliptra_ss_usb_usbd_conn`

## Overview

Verifies basic USB device connection detection via `DEVCMDSTAT.DCON` on the
hub-composite IP, in FS-only mode. This is a minimal connectivity smoke test:
no enumeration control transfers are issued by the host sequence, only link
bring-up and a passive observation window.

## Topology (hub-composite IP)

USBDC0 (the MCU-owned device controller) sits behind the on-chip 2-port USB
hub. Firmware brings the hub up in two phases:

1. `boot_usb_core()` programs USBDC0 and, internally via
   `usb_hub_init_and_connect()`, loads/validates the hub descriptor RAM and
   sets `HUB_EN`.
2. The test's `main()` then calls `usb_hub_connect()` to set `HUB_CONNECT`.
   Only after this does the host see the hub connect and drive VBUS/pull-up
   detection through to `DCON`.

Registers are accessed via the `USB_DEV0_*` bank (base `0x2000_1000`), not
the legacy `SOC_USBHSD_*` addresses (which now decode to the hub's small
register bank). The `USBHSD_DEVCMDSTAT_*_MASK` bit-mask macros are
unchanged.

## Operation

The UVM test class forces FS-only operation
(`high_speed_capable=0`, `host_cfg.speed = FS`, matching device/endpoint
speeds). The host sequence waits for the FS link to reach `ENABLED`, starts
SOF generation, and holds a 100 us observation window - it does not issue any
enumeration control transfers. In parallel, MCU firmware boots the hub +
USBDC0, then polls `DEVCMDSTAT.DCON` (servicing any incidental EP0
SETUP/DEV_INT along the way) until it observes `DCON=1`, at which point it
logs PASSED and halts.

## What Is Verified

- Hub bring-up (`usb_hub_init_and_connect()` + `usb_hub_connect()`) results
  in `DEVCMDSTAT.DCON` asserting on USBDC0
- MCU firmware correctly polls and reads the `DCON` bit via `USB_DEV0_*`
- FS link-up (pull-up detection) completes without HS chirp

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_usbd_conn_sequence.svh` | SVT VIP FS link-up + observation-window sequence (no enumeration transfers) |
| `caliptra_ss_usb_usbd_conn_test.svh` | UVM test class (forces FS-only speed) |
| `caliptra_ss_usb_usbd_conn.c` | MCU firmware: hub + USBDC0 bring-up, polls `DEVCMDSTAT.DCON` |
| `caliptra_ss_usb_usbd_conn.yml` | Simulation run config |
