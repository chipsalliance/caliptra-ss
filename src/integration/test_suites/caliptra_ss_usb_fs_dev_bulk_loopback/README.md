# Full-Speed Bulk Loopback Test

**Testcase:** `caliptra_ss_usb_fs_dev_bulk_loopback`

## Overview

Verifies FS bulk data transfer integrity with a 64-byte OUT-to-IN loopback on
EP1, on the hub-composite IP.

## Topology (hub-composite IP)

USBDC0 sits behind the on-chip 2-port USB hub. Firmware calls
`boot_usb_core_fs()` (FS-only bring-up: sets `DEVCMDSTAT.PFSC` to suppress
device K-chirp, and also performs hub bring-up phase 1 - HUB RAM programming
+ `HUB_EN` - internally), then calls `usb_hub_connect()` (phase 2,
`HUB_CONNECT`) once USBDC0 is fully programmed. Registers use the
`USB_DEV0_*` bank (base `0x2000_1000`); `USB_EP_ENTRY_ABS_ADDR()` is used for
the EP1 OUT/IN buffer addresses so the DMA engine resolves the correct
absolute AXI address.

## Operation

The VIP host issues an explicit bus reset (the FS-only host VIP does not
drive one automatically), then performs the full hub-aware enumeration
sequence: enumerate the on-chip hub at address 1 (device/config/hub-class
descriptors, `SET_CONFIGURATION`), bring up hub downstream port 1
(`GetPortStatus` -> `ClearFeature(C_PORT_CONNECTION)` ->
`SetFeature(PORT_RESET)` -> `ClearFeature(C_PORT_RESET)`), then enumerate
USBDC0 (behind the hub) at address 2. Once enumerated, the host sends 64
bytes of bulk OUT data to EP1 (byte pattern `i = 0..63`). MCU firmware
detects the EP1 OUT interrupt, copies the received data to the EP1 IN
buffer, and arms EP1 IN. The VIP host then reads back 64 bytes from EP1 IN
and checks it against the original pattern.

## What Is Verified

- Hub-aware enumeration in FS mode: hub @address 1, downstream port 1
  bring-up, USBDC0 @address 2
- FS bulk OUT transfer to EP1 (64 bytes, FS max packet size)
- MCU firmware loopback copy from EP1 OUT to EP1 IN buffer
- FS bulk IN transfer from EP1 (64 bytes read back by VIP host)
- End-to-end data integrity of 64 bytes

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_fs_dev_bulk_loopback_sequence.svh` | SVT VIP: explicit bus reset, hub-aware enumeration (hub @1, port bring-up, USBDC0 @2), bulk OUT+IN loopback |
| `caliptra_ss_usb_fs_dev_bulk_loopback_test.svh` | UVM test class (FS-only) |
| `caliptra_ss_usb_fs_dev_bulk_loopback.c` | MCU firmware loopback handler |
| `caliptra_ss_usb_fs_dev_bulk_loopback.yml` | Simulation run config |
