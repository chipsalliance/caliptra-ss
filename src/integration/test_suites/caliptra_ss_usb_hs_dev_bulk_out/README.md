# High-Speed Bulk OUT Transfer Test

**Testcase:** `caliptra_ss_usb_hs_dev_bulk_out`

## Overview

Verifies HS bulk OUT transfer of 2048 bytes with full data integrity check,
on the hub-composite IP.

## Topology (hub-composite IP)

USBDC0 sits behind the on-chip 2-port USB hub. `boot_usb_core()` programs
USBDC0's EP list/DEVCMDSTAT/DCON and, internally via
`usb_hub_init_and_connect()`, brings the hub up in phase 1 (HUB RAM +
`HUB_EN`). The test's `main()` then calls `usb_hub_connect()` (phase 2,
`HUB_CONNECT`) so the host can see the hub and begin enumerating its
downstream port. Registers use the `USB_DEV0_*` bank (base `0x2000_1000`);
the EP1 OUT buffer address uses `USB_EP_ENTRY_ABS_ADDR()`.

## Operation

The VIP host performs the full hub-aware enumeration: enumerate the on-chip
hub at address 1 (device/config/hub-class descriptors, `SET_CONFIGURATION`),
bring up hub downstream port 1 (`GetPortStatus` ->
`ClearFeature(C_PORT_CONNECTION)` -> `SetFeature(PORT_RESET)` ->
`ClearFeature(C_PORT_RESET)`), then enumerate USBDC0 (behind the hub) at
address 2. Once enumerated, the host sends 2048 bytes of bulk OUT data to
EP1 (pattern: `word[i] = i`, 512 words x 4 bytes, HS 4 x 512-byte packets).
MCU firmware receives the data, verifies each 32-bit word against the
pattern, and logs PASSED. The firmware event loop keeps servicing EP0/DEV
interrupts after the bulk transfer completes rather than exiting
immediately (matching the reference `janus_ahb_fw_bfm.sv` never-exiting
`service_irq()` behavior).

## What Is Verified

- Hub-aware enumeration: hub @address 1, downstream port 1 bring-up, USBDC0
  @address 2
- HS bulk OUT transfer of 2048 bytes to EP1
- Data integrity: each 32-bit word verified against incrementing pattern
  (`word[i] == i`)
- MCU firmware DMA reception and pattern checking
- EP0/DEV interrupt servicing continues after bulk completion (no early
  loop exit)

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev_bulk_out_sequence.svh` | SVT VIP: hub-aware enumeration (hub @1, port bring-up, USBDC0 @2), HS bulk OUT sequence (2048 bytes) |
| `caliptra_ss_usb_hs_dev_bulk_out_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_dev_bulk_out.c` | MCU firmware data verification |
| `caliptra_ss_usb_hs_dev_bulk_out.yml` | Simulation run config |
