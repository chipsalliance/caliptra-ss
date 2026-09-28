# USB GET_DESCRIPTOR(DEVICE) Test (Full-Speed)

**Testcase:** `caliptra_ss_usb_fs_dev_get_device_descriptor`

## Overview

Boots the MCU, brings up the USB hub-composite IP (HUB RAM programming,
HUB_EN, then HUB_CONNECT) and Caliptra core, enumerates the hub and USBDC0
through the hub (identical bring-up to `caliptra_ss_usb_init`), then issues a
standard GET_DESCRIPTOR(DEVICE) control transfer to BOTH the hub and dev0.
This is the Full-Speed variant; the test class forces the VIP into FS-only
mode (`high_speed_capable=0`) and the firmware boots via `boot_usb_core_fs()`
(sets DEVCMDSTAT.PFSC to suppress the device-side K-chirp) so the link
negotiates and stays at full speed (12 Mbit/s).

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

- USB hub-composite bring-up and enumeration (hub + USBDC0) at Full Speed
- GET_DESCRIPTOR(DEVICE) 18-byte device-descriptor parsing and check for the
  hub and for dev0

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_get_device_descriptor_sequence.svh` | Hub-aware enumeration + GET_DESCRIPTOR(DEVICE) VIP sequence (hub + dev0) |
| `caliptra_ss_usb_fs_dev_get_device_descriptor_test.svh` | FS UVM test class (FS-only VIP conversion + selects the sequence as default_sequence) |
| `caliptra_ss_usb_fs_dev_get_device_descriptor.c` | MCU firmware: FS hub bring-up (`boot_usb_core_fs()`) + EP0 event loop |
| `caliptra_ss_usb_fs_dev_get_device_descriptor.yml` | Simulation run config |
