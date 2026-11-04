# USB Hub GetDescriptor(BOS) Test (High-Speed)

**Testcase:** `caliptra_ss_usb_hs_dev_get_bos_descriptor`

## Overview

Boots the MCU, brings up the USB hub-composite IP (HUB RAM programming,
HUB_EN, then HUB_CONNECT) and Caliptra core, enumerates the hub and USBDC0
through the hub (identical bring-up to `caliptra_ss_usb_init`), then issues
GetDescriptor(BOS) control transfers to the hub. This is the High-Speed
variant; the link attaches at HS (480 Mbit/s) using the default VIP
configuration.

This test is the stimulus half of the BOS descriptor support added to the
`release_2.6` hub IP. Before it existed, `check_bos_descriptor()` in
`caliptra_ss_usb_data_check_api_impl.svh` was implemented but never called by
any test, so none of its assertions could fire.

## Operation

After enumeration completes (hub at address 1, USBDC0/dev0 at address 2), the
VIP host sequence `caliptra_ss_usb_get_bos_descriptor_sequence`:

1. Re-anchors the host agent onto the hub address (1).
2. Issues a **GetDescriptor(BOS) short read** (GET_DESCRIPTOR, wValue=0x0F00
   for BOS index 0, wLength=0x0005). This is the first half of the normal
   two-step host flow for a variable-length descriptor: fetch the 5-byte
   header to learn `wTotalLength`, then come back for the whole object. The
   payload length is checked locally to confirm the IP truncates the
   control-read at exactly the requested `wLength`.
3. Issues the **full GetDescriptor(BOS) read** (wLength=0x000C / 12 bytes) and
   hands the result to `check_bos_descriptor(.device_name("hub"))`.

Only the full read goes to the checker: `check_bos_descriptor()` asserts a
12-byte payload (`CHK_BOS_NUM_BYTES`), so passing it the 5-byte short read
would be a false failure.

## Expected Descriptor

The 12-byte response mirrors the BOS DESCRIPTOR block of the hub ROM constant
(table words 80..82, byte offset 0x140) in
`third_party/usb2/src/usb_hub_composite_device/RTL/RTL/usb_ep0_hub_descr.m.vhdl`:

| Offset | Field | Expected |
|--------|-------|----------|
| 0 | `bLength` (BOS header) | 0x05 |
| 1 | `bDescriptorType` | 0x0F (BOS) |
| 3:2 | `wTotalLength` (LE) | 0x000C |
| 4 | `bNumDeviceCaps` | 0x01 |
| 5 | `bLength` (capability) | 0x07 |
| 6 | `bDescriptorType` | 0x10 (DEVICE_CAPABILITY) |
| 7 | `bDevCapabilityType` | 0x02 (USB 2.0 Extension) |
| 11:8 | `bmAttributes` (LE) | 0x0000_0002 (bit1 = LPM supported) |

The request is only legal because the hub DEVICE descriptor reports
bcdUSB=0x0210: per the USB 2.0 LPM ECN a device must report bcdUSB >= 0x0201
before a host may ask for the BOS. That bcdUSB bump arrived in the same hub IP
release that moved the hub control/status word from table word 15 to word 12.

## Firmware

The BOS request is addressed to the hub and is answered entirely by the hub
EP0 hardware out of its descriptor ROM; it never reaches the MCU. The firmware
therefore needs no BOS-specific logic - it only runs the standard poll loop,
servicing every SETUP aimed at USBDC0 via `usb_handle_control_transfer()` (in
the shared `libs/usb/usb.c`) and re-arming EP0 OUT on any non-SETUP EP0-OUT
interrupt (status-stage ZLP) so the next SETUP is not silently dropped.

## What Is Verified

- USB hub-composite bring-up and enumeration (hub + USBDC0)
- GetDescriptor(BOS) short read is truncated to the requested 5 bytes
- All 8 fields of the hub BOS descriptor match the RTL ROM
- `cg_bos_descriptor` functional coverage is sampled for the hub

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_get_bos_descriptor_sequence.svh` | Hub-aware enumeration + GetDescriptor(BOS) VIP sequence |
| `caliptra_ss_usb_hs_dev_get_bos_descriptor_test.svh` | HS UVM test class (selects the sequence as default_sequence) |
| `caliptra_ss_usb_hs_dev_get_bos_descriptor.c` | MCU firmware: hub bring-up + EP0 event loop |
| `caliptra_ss_usb_hs_dev_get_bos_descriptor.yml` | Simulation run config |

## Related

`caliptra_ss_usb_fs_dev_get_bos_descriptor` is the Full-Speed sibling. It runs
the same sequence with the FS VIP conversion applied; the BOS descriptor is
speed-independent, so both variants check identical ROM contents.
