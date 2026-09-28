# USB GetHubDescriptor Test (Full-Speed)

**Testcase:** `caliptra_ss_usb_fs_dev_get_hub_descriptor`

## Overview

Boots the MCU, brings up the USB hub-composite IP (HUB RAM programming,
HUB_EN, then HUB_CONNECT) and Caliptra core, enumerates the hub and USBDC0
through the hub (identical bring-up to `caliptra_ss_usb_init`), then issues a
hub-class GetHubDescriptor control transfer to the hub. This is the Full-Speed
variant: the VIP is forced FS-only (`high_speed_capable=0`) and the firmware
uses `boot_usb_core_fs()` (sets DEVCMDSTAT.PFSC, bit 21) so the device
suppresses the K-chirp and the link attaches and stays at full speed. The Hub
Class Descriptor is speed-independent, so the returned bytes and the scoreboard
checks are identical to the HS variant.

## Operation

After enumeration completes (hub at address 1, USBDC0/dev0 at address 2), the
VIP host sequence `caliptra_ss_usb_get_hub_descriptor_sequence` (shared with the
HS variant):

1. Re-anchors the host agent onto the hub address (1).
2. Issues a **GetHubDescriptor** for the hub (hub-class GET_DESCRIPTOR,
   recipient=device, wValue=0x2900 selecting descriptor type 0x29 = Hub Class
   Descriptor index 0, wLength=9), returning the 9-byte Hub Class Descriptor,
   checked with `check_hub_descriptor`.

The expected 9 bytes are sourced from the hub descriptor flip-flop array (ROM
default in `usb_ep0_hub_descr.m.vhdl`) with the firmware CLASS-descriptor
override applied in `usb_hub_init_and_connect()` before HUB_CONNECT. They are
speed-independent:

| Byte | Field | Value |
|------|-------|-------|
| 0 | bDescLength | 0x09 |
| 1 | bDescriptorType | 0x29 |
| 2 | bNbrPorts | 0x02 |
| 3-4 | wHubCharacteristics (LE) | 0x0014 |
| 5 | bPwrOn2PwrGood | 0x32 |
| 6 | bHubContrCurrent | 0x64 |
| 7 | DeviceRemovable | 0x0A |
| 8 | PortPwrCtrlMask | 0xFF |

## What Is Verified

- USB hub-composite bring-up and FS enumeration (hub + USBDC0)
- GetHubDescriptor (9-byte Hub Class Descriptor) parsing and field checks

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_get_hub_descriptor_sequence.svh` | Hub-aware enumeration + GetHubDescriptor VIP sequence (shared with HS) |
| `caliptra_ss_usb_fs_dev_get_hub_descriptor_test.svh` | FS UVM test class (forces FS-only VIP, selects the sequence as default_sequence) |
| `caliptra_ss_usb_fs_dev_get_hub_descriptor.c` | MCU firmware: FS hub bring-up (boot_usb_core_fs) + EP0 event loop |
| `caliptra_ss_usb_fs_dev_get_hub_descriptor.yml` | Simulation run config |
