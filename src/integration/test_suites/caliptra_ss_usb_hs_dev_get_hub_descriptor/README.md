# USB GetHubDescriptor Test (High-Speed)

**Testcase:** `caliptra_ss_usb_hs_dev_get_hub_descriptor`

## Overview

Boots the MCU, brings up the USB hub-composite IP (HUB RAM programming,
HUB_EN, then HUB_CONNECT) and Caliptra core, enumerates the hub and USBDC0
through the hub (identical bring-up to `caliptra_ss_usb_init`), then issues a
hub-class GetHubDescriptor control transfer to the hub. This is the High-Speed
variant; the link attaches at HS (480 Mbit/s) using the default VIP
configuration.

## Operation

After enumeration completes (hub at address 1, USBDC0/dev0 at address 2), the
VIP host sequence `caliptra_ss_usb_get_hub_descriptor_sequence`:

1. Re-anchors the host agent onto the hub address (1).
2. Issues a **GetHubDescriptor** for the hub (hub-class GET_DESCRIPTOR,
   recipient=device, wValue=0x2900 selecting descriptor type 0x29 = Hub Class
   Descriptor index 0, wLength=9), returning the 9-byte Hub Class Descriptor,
   checked with `check_hub_descriptor`.

The expected 9 bytes come from the hub ROM (`usb_ep0_hub_descr.m.vhdl`) and are
speed-independent:

| Byte | Field | Value |
|------|-------|-------|
| 0 | bDescLength | 0x09 |
| 1 | bDescriptorType | 0x29 |
| 2 | bNbrPorts | 0x02 |
| 3-4 | wHubCharacteristics (LE) | 0x0014 |
| 5 | bPwrOn2PwrGood | 0x00 |
| 6 | bHubContrCurrent | 0x00 |
| 7 | DeviceRemovable | 0x06 |
| 8 | PortPwrCtrlMask | 0xFF |

## What Is Verified

- USB hub-composite bring-up and enumeration (hub + USBDC0)
- GetHubDescriptor (9-byte Hub Class Descriptor) parsing and field checks

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_get_hub_descriptor_sequence.svh` | Hub-aware enumeration + GetHubDescriptor VIP sequence |
| `caliptra_ss_usb_hs_dev_get_hub_descriptor_test.svh` | HS UVM test class (selects the sequence as default_sequence) |
| `caliptra_ss_usb_hs_dev_get_hub_descriptor.c` | MCU firmware: hub bring-up + EP0 event loop |
| `caliptra_ss_usb_hs_dev_get_hub_descriptor.yml` | Simulation run config |
