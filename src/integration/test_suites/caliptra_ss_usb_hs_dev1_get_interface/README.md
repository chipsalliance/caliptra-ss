# USB GetInterface Test (High-Speed, USBDC1)

**Testcase:** `caliptra_ss_usb_hs_dev1_get_interface`

## Overview

USBDC1 (device1) variant of `caliptra_ss_usb_hs_dev_get_interface`. Boots the
MCU, brings up the USB hub-composite IP (HUB RAM programming, HUB_EN, then
HUB_CONNECT) and Caliptra core, enumerates the hub and USBDC1 through hub
downstream **port 2**, then issues a standard **GET_INTERFACE** control
transfer to the hub and to USBDC1. This is the High-Speed variant; the link
attaches at HS (480 Mbit/s) using the default VIP configuration. There is no FS
dev1 variant (the compound shares a single link engine that defaults to High
Speed - see `claude_md/15_usb_dev1_replication.md`).

The firmware is identical in structure to the USBDC0 test; the shared USB
library is retargeted to the USBDC1 aperture purely by `-DUSB_DEV_SEL=1`,
passed from the yml through `BUILD_CFLAGS`.

## Operation

After enumeration completes (hub at address 1, USBDC1/dev1 at address 2), the
VIP host sequence `caliptra_ss_usb_hs_dev1_get_interface_sequence`:

1. Re-anchors the host agent onto the hub address (1), issues a
   **GET_INTERFACE** request (bmRequestType=0x81 IN/STANDARD/INTERFACE,
   bRequest=0x0A, wValue=0x0000, wIndex=0x0000 = interface 0, wLength=0x0001)
   and checks the single returned byte with
   `caliptra_ss_usb_data_check_api::check_get_interface` (device_name `"hub"`,
   expected bAlternateSetting = 0x00).
2. Re-anchors onto the dev1 address (2) and repeats the same request, checked
   with device_name `"dev1"`.

The two targets answer from different sources:

- **Hub:** entirely in EP0 hardware. The hub EP0 ROM SETUP-match table
  contains a GetInterface entry (`X"00000A81"`, opcode 0x06, data-phase length
  1) and `usb_ep0_handler.m.vhdl` drives
  `setup_data(7 downto 0) <= (others => '0')` for `C_STD_REQ_GET_INTERFACE`
  because the hub exposes a single interface with one alternate setting.
- **dev1:** from the shared EP0 dispatcher in `test_suites/libs/usb/usb.c`.
  `USB_REQ_GET_INTERFACE` returns the per-controller `usb_alt_setting` shadow
  (one byte), gated on the Configured state and `wIndex == 0`. The shadow is
  indexed by the active controller, so the same handler serves dev0 and dev1
  with no firmware delta.

`SET_INTERFACE` is still stalled by the device firmware and is not exercised
here.

## What Is Verified

- USB hub-composite bring-up and enumeration of the hub + USBDC1 (port 2)
- Standard GET_INTERFACE response from the hub: exactly one data byte, 0x00
- Standard GET_INTERFACE response from dev1: exactly one data byte, 0x00

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev1_get_interface_sequence.svh` | Hub + USBDC1 enumeration and GET_INTERFACE VIP sequence |
| `caliptra_ss_usb_hs_dev1_get_interface_test.svh` | HS UVM test class (selects the sequence as default_sequence) |
| `caliptra_ss_usb_hs_dev1_get_interface.c` | MCU firmware: hub bring-up + EP0 poll loop (built with `-DUSB_DEV_SEL=1`) |
| `caliptra_ss_usb_hs_dev1_get_interface.yml` | Simulation run config (passes `BUILD_CFLAGS="-DUSB_DEV_SEL=1"`) |
