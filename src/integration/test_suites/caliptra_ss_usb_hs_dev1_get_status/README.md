# USB GET_STATUS Test (High-Speed, USBDC1)

**Testcase:** `caliptra_ss_usb_hs_dev1_get_status`

## Overview

Boots the MCU, brings up the USB hub-composite IP (HUB RAM programming,
HUB_EN, then HUB_CONNECT) and Caliptra core, enumerates the hub and USBDC1
through hub downstream port 2 (identical bring-up to `caliptra_ss_usb_init`),
then exercises SetFeature / ClearFeature(DEVICE_REMOTE_WAKEUP) + GET_STATUS on
the enumerated devices. This is the High-Speed variant; the link attaches at
HS (480 Mbit/s) using the default VIP configuration.

This is the USBDC1 (device1) counterpart of
`caliptra_ss_usb_hs_dev_get_status`. It differs from the USBDC0 test in exactly
two ways: the host sequence brings up hub downstream port 2 (USBDC1) and checks
the addressed device as "dev1", and the firmware is built with
`-DUSB_DEV_SEL=1` so the shared USB library targets the USBDC1 aperture
(regs 0x2001_0000, DMA 0x2001_0100). See
`claude_md/15_usb_dev1_replication.md`.

## Operation

After enumeration completes (hub at address 1, USBDC1/dev1 at address 2), the
VIP host sequence `caliptra_ss_usb_hs_dev1_get_status_sequence`:

1. Issues **SetFeature(DEVICE_REMOTE_WAKEUP)** followed by **GET_STATUS** for
   the hub (address 1), checked with `check_get_status` against `0x0002`.
2. Issues **SetFeature(DEVICE_REMOTE_WAKEUP)** followed by **GET_STATUS** for
   dev1 (address 2), checked against `0x0002` (bit1 = Remote-Wakeup).
3. Issues **ClearFeature(DEVICE_REMOTE_WAKEUP)** followed by **GET_STATUS** for
   dev1, checked against `0x0000` (Remote-Wakeup disabled).

The hub is separate RTL (`third_party/usb_hub_composite_device`), not MCU
firmware, so its GET_STATUS response is fixed by the hub RTL.

MCU firmware services every SETUP via `usb_handle_control_transfer()` (in the
shared `libs/usb/usb.c`) and re-arms EP0 OUT on any non-SETUP EP0-OUT
interrupt (status-stage ZLP) so the next SETUP is not silently dropped. The
SET_FEATURE / CLEAR_FEATURE / GET_STATUS handling lives entirely in that shared
dispatcher; no test-specific firmware logic is required.

## What Is Verified

- USB hub-composite bring-up and enumeration (hub + USBDC1 via port 2)
- SET_FEATURE(DEVICE_REMOTE_WAKEUP) firmware handling and its reflection in
  the subsequent 2-byte GET_STATUS response (dev1 = 0x0002)
- CLEAR_FEATURE(DEVICE_REMOTE_WAKEUP) firmware handling and GET_STATUS = 0x0000

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev1_get_status_sequence.svh` | Hub-aware enumeration (port 2) + get_status VIP sequence |
| `caliptra_ss_usb_hs_dev1_get_status_test.svh` | HS UVM test class (selects the sequence as default_sequence) |
| `caliptra_ss_usb_hs_dev1_get_status.c` | MCU firmware: hub bring-up + EP0 event loop |
| `caliptra_ss_usb_hs_dev1_get_status.yml` | Simulation run config (BUILD_CFLAGS=-DUSB_DEV_SEL=1) |

> Generated from `caliptra_ss_usb_hs_dev_get_status` (USBDC1 counterpart). Firmware is retargeted to the USBDC1 aperture by `-DUSB_DEV_SEL=1` and the host sequence brings up hub downstream port 2.
