# USB GET_DESCRIPTOR(DEVICE) Test (High-Speed, USBDC1)

**Testcase:** `caliptra_ss_usb_hs_dev1_get_device_descriptor`

## Overview

Boots the MCU, brings up the USB hub-composite IP (HUB RAM programming,
HUB_EN, then HUB_CONNECT) and Caliptra core, enumerates the hub and USBDC1
through hub downstream port 2 (identical bring-up to `caliptra_ss_usb_init`),
then issues a standard GET_DESCRIPTOR(DEVICE) control transfer to BOTH the hub
and dev1. This is the High-Speed variant; the link attaches at HS (480 Mbit/s)
using the default VIP configuration.

This is the USBDC1 (device1) counterpart of
`caliptra_ss_usb_hs_dev_get_device_descriptor`. It differs from the USBDC0 test
in exactly two ways: the host sequence brings up hub downstream port 2 (USBDC1)
and checks the addressed device as "dev1", and the firmware is built with
`-DUSB_DEV_SEL=1` so the shared USB library targets the USBDC1 aperture
(regs 0x2001_0000, DMA 0x2001_0100). See
`claude_md/15_usb_dev1_replication.md`.

## Operation

After enumeration completes (hub at address 1, USBDC1/dev1 at address 2), the
VIP host sequence `caliptra_ss_usb_hs_dev1_get_device_descriptor_sequence`:

1. Re-anchors the host agent onto the hub address (1) and issues a
   **GET_DESCRIPTOR(DEVICE)** for the hub (standard request, bRequest=0x06,
   wValue=0x0100 (descriptor type 1 = DEVICE, index 0), wLength=0x0012
   (18 bytes)), checked with `check_device_descriptor`.
2. Re-anchors the host agent onto the dev1 address (2) and issues the same
   **GET_DESCRIPTOR(DEVICE)** for dev1, checked with `check_device_descriptor`.

## What Is Verified

- USB hub-composite bring-up and enumeration (hub + USBDC1 via port 2)
- GET_DESCRIPTOR(DEVICE) 18-byte device-descriptor parsing and check for the
  hub and for dev1

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev1_get_device_descriptor_sequence.svh` | Hub-aware enumeration (port 2) + GET_DESCRIPTOR(DEVICE) VIP sequence (hub + dev1) |
| `caliptra_ss_usb_hs_dev1_get_device_descriptor_test.svh` | HS UVM test class (selects the sequence as default_sequence) |
| `caliptra_ss_usb_hs_dev1_get_device_descriptor.c` | MCU firmware: hub bring-up + EP0 event loop |
| `caliptra_ss_usb_hs_dev1_get_device_descriptor.yml` | Simulation run config (BUILD_CFLAGS=-DUSB_DEV_SEL=1) |

> Generated from `caliptra_ss_usb_hs_dev_get_device_descriptor` (USBDC1 counterpart). Firmware is retargeted to the USBDC1 aperture by `-DUSB_DEV_SEL=1` and the host sequence brings up hub downstream port 2.
