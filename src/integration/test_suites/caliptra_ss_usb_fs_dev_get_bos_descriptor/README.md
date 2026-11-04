# USB Hub GetDescriptor(BOS) Test (Full-Speed)

**Testcase:** `caliptra_ss_usb_fs_dev_get_bos_descriptor`

## Overview

Full-speed variant of `caliptra_ss_usb_hs_dev_get_bos_descriptor`. It runs the
identical `caliptra_ss_usb_get_bos_descriptor_sequence` but the UVM test forces
the VIP into FS-only mode (`high_speed_capable=0`) and re-stamps the default
endpoints to FS so `cfg.is_valid()` passes; the firmware brings the USB core up
with `boot_usb_core_fs()` (DEVCMDSTAT.PFSC set to suppress the device-side
K-chirp) so the link negotiates and stays at full speed.

The BOS descriptor is speed-independent: it lives in the hub descriptor ROM and
is returned at either speed. Running this variant alongside the HS one proves
the descriptor fetch does not depend on the HS chirp path.

## Operation

Same three steps as the HS variant. After enumeration (hub at address 1,
USBDC0/dev0 at address 2) the sequence:

1. Re-anchors the host agent onto the hub address (1).
2. Issues a **GetDescriptor(BOS) short read** (wValue=0x0F00, wLength=0x0005)
   and verifies the response is truncated to the requested 5 bytes.
3. Issues the **full read** (wLength=0x000C / 12 bytes) and hands it to
   `check_bos_descriptor(.device_name("hub"))`.

Expected field values are identical to the HS variant - see that test's README
for the full table. In short: BOS header `bLength=0x05`,
`bDescriptorType=0x0F`, `wTotalLength=0x000C`, `bNumDeviceCaps=0x01`, followed
by a USB 2.0 Extension capability (`bLength=0x07`, `bDescriptorType=0x10`,
`bDevCapabilityType=0x02`, `bmAttributes=0x0000_0002` with bit1 = LPM).

## Firmware

Pure polling loop with no ISR involvement (no `mcu_isr.h`, no
`init_usb_interrupts()`, no ISR mailbox), structured like
`caliptra_ss_usb_fs_conn.c`: INTSTAT is read each iteration and each serviced
bit (DEV_INT, EP0OUT, EP0IN) is write-1-to-cleared. The BOS request itself is
answered by the hub EP0 hardware and never reaches the MCU, so there is no
BOS-specific firmware logic.

## What Is Verified

- USB hub-composite bring-up and enumeration at full speed (hub + USBDC0)
- GetDescriptor(BOS) short read is truncated to the requested 5 bytes
- All 8 fields of the hub BOS descriptor match the RTL ROM at FS
- `cg_bos_descriptor` functional coverage is sampled for the hub

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_get_bos_descriptor_sequence.svh` | Hub-aware enumeration + GetDescriptor(BOS) VIP sequence (shared with the HS variant) |
| `caliptra_ss_usb_fs_dev_get_bos_descriptor_test.svh` | FS UVM test class (FS VIP conversion + selects the sequence) |
| `caliptra_ss_usb_fs_dev_get_bos_descriptor.c` | MCU firmware: FS hub bring-up + polled EP0 event loop |
| `caliptra_ss_usb_fs_dev_get_bos_descriptor.yml` | Simulation run config |
