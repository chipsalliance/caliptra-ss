# USB GetInterface Test (High-Speed)

**Testcase:** `caliptra_ss_usb_hs_dev_get_interface`

## Overview

Boots the MCU, brings up the USB hub-composite IP (HUB RAM programming,
HUB_EN, then HUB_CONNECT) and Caliptra core, enumerates the hub and USBDC0
through the hub (identical bring-up to `caliptra_ss_usb_init`), then issues a
standard **GET_INTERFACE** control transfer to the hub. This is the High-Speed
variant; the link attaches at HS (480 Mbit/s) using the default VIP
configuration.

## Operation

After enumeration completes (hub at address 1, USBDC0/dev0 at address 2), the
VIP host sequence `caliptra_ss_usb_get_interface_sequence`:

1. Re-anchors the host agent onto the hub address (1).
2. Issues a **GET_INTERFACE** request (bmRequestType=0x81
   IN/STANDARD/INTERFACE, bRequest=0x0A, wValue=0x0000, wIndex=0x0000 =
   interface 0, wLength=0x0001) and checks the single returned byte with
   `caliptra_ss_usb_data_check_api::check_get_interface` (expected
   bAlternateSetting = 0x00).

The request is answered entirely by the hub EP0 hardware: the hub EP0 ROM
SETUP-match table contains a GetInterface entry (`X"00000A81"`, opcode 0x06,
data-phase length 1) and `usb_ep0_handler.m.vhdl` drives
`setup_data(7 downto 0) <= (others => '0')` for `C_STD_REQ_GET_INTERFACE`
because the hub exposes a single interface with one alternate setting.
No test-specific MCU firmware logic is required.

Note: the embedded device controllers (USBDC0/USBDC1) stall GET_INTERFACE in
firmware (`test_suites/libs/usb/usb.c`), so only the hub is a valid target for
this request.

## What Is Verified

- USB hub-composite bring-up and enumeration (hub + USBDC0)
- Standard GET_INTERFACE response: exactly one data byte, value 0x00

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_get_interface_sequence.svh` | Hub-aware enumeration + GET_INTERFACE VIP sequence |
| `caliptra_ss_usb_hs_dev_get_interface_test.svh` | HS UVM test class (selects the sequence as default_sequence) |
| `caliptra_ss_usb_hs_dev_get_interface.c` | MCU firmware: hub bring-up + EP0 event loop |
| `caliptra_ss_usb_hs_dev_get_interface.yml` | Simulation run config |
