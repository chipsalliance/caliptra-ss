# USB GET_DESCRIPTOR(DEVICE) Test (High-Speed)

**Testcase:** `caliptra_ss_usb_hs_dev_get_device_descriptor`

## Overview

Boots the MCU, brings up the USB hub-composite IP (HUB RAM programming,
HUB_EN, then HUB_CONNECT) and Caliptra core, enumerates the hub and USBDC0
through the hub (identical bring-up to `caliptra_ss_usb_init`), then issues a
standard GET_DESCRIPTOR(DEVICE) control transfer to BOTH the hub and dev0.
This is the High-Speed variant; the link attaches at HS (480 Mbit/s) using
the default VIP configuration.

## Operation

After enumeration completes (hub at address 1, USBDC0/dev0 at address 2), the
VIP host sequence `caliptra_ss_usb_get_device_descriptor_sequence`:

1. Re-anchors the host agent onto the hub address (1) and issues a
   **GET_DESCRIPTOR(DEVICE)** for the hub (standard request, bRequest=0x06,
   wValue=0x0100 (descriptor type 1 = DEVICE, index 0), wLength=0x0012
   (18 bytes)), checked with `check_device_descriptor`.
2. Re-anchors the host agent onto the dev0 address (2) and issues the same
   **GET_DESCRIPTOR(DEVICE)** for dev0, checked with `check_device_descriptor`.

## What Is Verified

- USB hub-composite bring-up and enumeration (hub + USBDC0)
- GET_DESCRIPTOR(DEVICE) 18-byte device-descriptor parsing and check for the
  hub and for dev0

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_get_device_descriptor_sequence.svh` | Hub-aware enumeration + GET_DESCRIPTOR(DEVICE) VIP sequence (hub + dev0) |
| `caliptra_ss_usb_hs_dev_get_device_descriptor_test.svh` | HS UVM test class (selects the sequence as default_sequence) |
| `caliptra_ss_usb_hs_dev_get_device_descriptor.c` | MCU firmware: hub bring-up + EP0 event loop |
| `caliptra_ss_usb_hs_dev_get_device_descriptor.yml` | Simulation run config |
