# USB GetHubStatus Test (Full-Speed)

**Testcase:** `caliptra_ss_usb_fs_dev_get_hub_status`

## Overview

Boots the MCU, brings up the USB hub-composite IP (HUB RAM programming,
HUB_EN, then HUB_CONNECT) and Caliptra core, enumerates the hub and USBDC0
through the hub (identical bring-up to `caliptra_ss_usb_init`), then issues a
hub-class GetHubStatus control transfer to the hub. This is the Full-Speed
variant; the link attaches at FS (12 Mbit/s) using the FS-only VIP
configuration (high_speed_capable=0).

## Operation

After enumeration completes (hub at address 1, USBDC0/dev0 at address 2), the
VIP host sequence `caliptra_ss_usb_get_hub_status_sequence`:

1. Re-anchors the host agent onto the hub address (1).
2. Issues a **GetHubStatus** for the hub (hub-class GET_STATUS,
   recipient=device, wLength=4, 4-byte wHubStatus + wHubChange response),
   checked with `check_hub_status` (expected wHubStatus=0, wHubChange=0 fresh
   after enumeration).

## What Is Verified

- USB hub-composite bring-up and enumeration (hub + USBDC0)
- GetHubStatus (4-byte hub-class status) parsing and check

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_get_hub_status_sequence.svh` | Hub-aware enumeration + GetHubStatus VIP sequence |
| `caliptra_ss_usb_fs_dev_get_hub_status_test.svh` | FS UVM test class (selects the sequence as default_sequence) |
| `caliptra_ss_usb_fs_dev_get_hub_status.c` | MCU firmware: hub bring-up + EP0 event loop |
| `caliptra_ss_usb_fs_dev_get_hub_status.yml` | Simulation run config |
