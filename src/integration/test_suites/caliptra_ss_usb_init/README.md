# USB Device Controller Initialization Test

**Testcase:** `caliptra_ss_usb_init`

## Overview

Boots the MCU, brings up the USB hub-composite IP (HUB RAM programming,
HUB_EN, then HUB_CONNECT), and Caliptra core, then enumerates USBDC0 through
the hub. This is the canonical, control-plane-only device event loop: no data
endpoint, no suspend, no disconnect. It is the smallest/fastest smoke test
proving boot + EP0 bring-up + enumeration, and the reference firmware
structure that the other USB device tests were derived from.

## Operation

`boot_usb_core()` programs the HUB RAM descriptors and the USBDC0 EP list/
DEVCMDSTAT/DCON, and sets HUB_EN. After Caliptra core bring-up, firmware
calls `usb_hub_connect()` to set HUB_CONNECT, at which point the host sees
the hub on the bus. The VIP host sequence then:

1. Enumerates the hub itself at address 1 (device + configuration + hub-class
   descriptors, SET_CONFIGURATION).
2. Brings up hub downstream port 1 (where USBDC0 is attached) via hub-class
   GetPortStatus / ClearFeature(C_PORT_CONNECTION) / SetFeature(PORT_RESET) /
   ClearFeature(C_PORT_RESET).
3. Enumerates USBDC0 (behind the hub) at address 2: GET_DESCRIPTOR,
   GET_STATUS, SET_ADDRESS, GET_CONFIGURATION, SET_CONFIGURATION,
   GET_CONFIGURATION (verify).

MCU firmware services every SETUP via `usb_handle_control_transfer()` and
re-arms EP0 OUT on any non-SETUP EP0-OUT interrupt (status-stage ZLP) so the
next SETUP is not silently dropped.

## What Is Verified

- USB hub-composite bring-up: HUB RAM programming, HUB_EN, HUB_CONNECT
- Hub enumeration and downstream port bring-up (port reset / enable)
- USBDC0 enumeration behind the hub (GET_DESCRIPTOR / GET_STATUS /
  SET_ADDRESS / GET_CONFIGURATION / SET_CONFIGURATION)
- EP0 control-transfer event loop: SETUP detection, dispatch, and EP0 OUT
  re-arm on status-stage completion

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_init_sequence.svh` | Hub-aware SVT VIP enumeration sequence |
| `caliptra_ss_usb_basic_utmi_test.svh` | UVM test class (selects this sequence as default_sequence; note the naming quirk - firmware runs under `+UVM_TESTNAME=caliptra_ss_usb_basic_utmi_test`, not a name-matched test) |
| `caliptra_ss_usb_init.c` | MCU firmware: hub bring-up + EP0 event loop |
| `caliptra_ss_usb_init.yml` | Simulation run config |
