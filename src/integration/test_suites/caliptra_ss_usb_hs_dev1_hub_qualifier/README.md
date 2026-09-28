# USB Hub GetDeviceQualifier Test (High-Speed, USBDC1)

**Testcase:** `caliptra_ss_usb_hs_dev1_hub_qualifier`

## Overview

Boots the MCU, brings up the USB hub-composite IP (HUB RAM programming,
HUB_EN, then HUB_CONNECT) and Caliptra core, enumerates the hub and USBDC1
through hub downstream port 2 (identical bring-up to `caliptra_ss_usb_init`),
then issues a GetDeviceQualifier control transfer to the hub. This is the
High-Speed variant; the link attaches at HS (480 Mbit/s) using the default VIP
configuration.

This is the USBDC1 (device1) counterpart of
`caliptra_ss_usb_hs_dev_hub_qualifier`. It differs from the USBDC0 test in
exactly two ways: the host sequence brings up hub downstream port 2 (USBDC1),
and the firmware is built with `-DUSB_DEV_SEL=1` so the shared USB library
targets the USBDC1 aperture (regs 0x2001_0000, DMA 0x2001_0100). See
`claude_md/15_usb_dev1_replication.md`.

## Operation

After enumeration completes (hub at address 1, USBDC1/dev1 at address 2), the
VIP host sequence `caliptra_ss_usb_hs_dev1_hub_qualifier_sequence`:

1. Re-anchors the host agent onto the hub address (1).
2. Issues a **GetDeviceQualifier** for the hub (GET_DESCRIPTOR, wValue=0x0600
   for DEVICE_QUALIFIER index 0, wLength=0x000A / 10 bytes).

Per USB 2.0 spec 9.6.2, an HS-capable device returns the DEVICE_QUALIFIER
descriptor at either speed, so GetDeviceQualifier is issued with no speed
gating.

MCU firmware services every SETUP via `usb_handle_control_transfer()` (in the
shared `libs/usb/usb.c`) and re-arms EP0 OUT on any non-SETUP EP0-OUT
interrupt (status-stage ZLP) so the next SETUP is not silently dropped.

## What Is Verified

- USB hub-composite bring-up and enumeration (hub + USBDC1 via port 2)
- GetDeviceQualifier control transfer to the hub

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev1_hub_qualifier_sequence.svh` | Hub-aware enumeration (port 2) + GetDeviceQualifier VIP sequence |
| `caliptra_ss_usb_hs_dev1_hub_qualifier_test.svh` | HS UVM test class (selects the sequence as default_sequence) |
| `caliptra_ss_usb_hs_dev1_hub_qualifier.c` | MCU firmware: hub bring-up + EP0 event loop |
| `caliptra_ss_usb_hs_dev1_hub_qualifier.yml` | Simulation run config (BUILD_CFLAGS=-DUSB_DEV_SEL=1) |

> Generated from `caliptra_ss_usb_hs_dev_hub_qualifier` (USBDC1 counterpart). Firmware is retargeted to the USBDC1 aperture by `-DUSB_DEV_SEL=1` and the host sequence brings up hub downstream port 2.
