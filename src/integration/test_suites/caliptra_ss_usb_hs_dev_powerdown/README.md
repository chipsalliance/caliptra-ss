# High-Speed Device Power-Down Test

**Testcase:** `caliptra_ss_usb_hs_dev_powerdown`

## Overview

Verifies a genuine USB HS device power-down and power-up cycle on the
hub-composite IP. USBDC0 (the MCU-owned device controller) is an embedded
downstream device of the on-chip 2-port hub, so a real power-down is driven
as a hub-class `ClearFeature(PORT_ENABLE)` on USBDC0's downstream port
(port 1) - **not** a VBUS off/on cycle, which is how the legacy
single-device version of this test worked and which does not apply to this
topology.

## Topology and Power-Down Mechanism (hub-composite IP)

`ClearFeature(PORT_ENABLE)` on hub downstream port 1 clears
`hub_port_enable_int(0)` in the hub RTL (`usb_app_hw_hub.m.vhdl
PROC_REQUEST_HANDLING`). Per the compound-structure netlist, USBDC0's
controller enable is gated by that signal:
`usbreg_deviceenabled(1) <= hub_port_enable(0) and usbreg_arm_deviceenabled`,
so clearing port-enable de-gates USBDC0's device controller
(`deviceenabled=0`) - a real, waveform-visible power-down, not merely a
status-bit toggle. `PORT_POWER` and `PORT_SUSPEND` are no-ops on this IP and
would be a false pass if used instead.

Recovery is `SetFeature(PORT_RESET)` on the same port: this re-asserts
`hub_port_enable(0)` **and** pulses `hub_port_reset(0)`, which drives
`arm_dev_portreset` into USBDC0. USBDC0 therefore observes a genuine bus
reset (`DRES_C` set) and returns to the Default state, at which point the
host re-enumerates it.

USBDC0 stays VBUS-powered throughout (`FORCE_VBUS=1`, as programmed by
`boot_usb_core()`); the power-down is the controller-enable degate, and
recovery is proven by observing the recovery bus reset (`DRES_C`), not
merely by a bare re-enumeration.

## Operation

1. **Initial enumeration behind the hub.** Firmware services EP0 SETUP
   tokens and bus resets until `USB_ENUM_XFER_COUNT` (7) control transfers
   are handled: `GET_DESCRIPTOR(DEVICE)@addr0`, `GET_STATUS@addr0`,
   `SET_ADDRESS(2)@addr0`, `GET_DESCRIPTOR(DEVICE)@addr2`,
   `GET_CONFIGURATION@addr2`, `SET_CONFIGURATION(1)@addr2`,
   `GET_CONFIGURATION(verify)@addr2`.
2. **Power-down.** The VIP host issues `ClearFeature(PORT_ENABLE)` on hub
   port 1. This is a hub-side event and does **not** raise a USBDC0
   interrupt - USBDC0 simply goes quiet on the bus. Firmware records the bus
   reset count observed so far (`usb_bus_reset_count`) as a baseline.
3. **Recovery.** The VIP host issues `SetFeature(PORT_RESET)` on hub port 1.
   Firmware observes the resulting `DRES_C` bus reset on USBDC0 (via
   `usb_handle_bus_reset()`, which increments `usb_bus_reset_count`) and
   then services the same 7-transfer re-enumeration sequence as step 1.
4. Firmware asserts that `usb_bus_reset_count` advanced past the baseline
   recorded in step 2 - this is what distinguishes a genuine power-cycle
   from a bare re-enumeration false pass. Prints
   `USB HS device powerdown PASSED` once both the recovery bus reset and
   re-enumeration are confirmed.

## What Is Verified

- Hub-class `ClearFeature(PORT_ENABLE)` genuinely de-gates USBDC0's device
  controller (not just a status-bit toggle)
- `SetFeature(PORT_RESET)` recovery both re-enables the port and drives a
  real bus reset (`DRES_C`) into USBDC0
- The recovery bus reset is explicitly counted and asserted on, so the pass
  cannot be a bare re-enumeration
- Full 7-transfer enumeration completes both before power-down and after
  recovery
- `FORCE_VBUS` remains set throughout (USBDC0 is never actually VBUS-power-
  cycled - only its hub-side port-enable is)

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev_powerdown_sequence.svh` | SVT VIP: hub-aware enumeration, `ClearFeature(PORT_ENABLE)` power-down, `SetFeature(PORT_RESET)` recovery on hub port 1 |
| `caliptra_ss_usb_hs_dev_powerdown_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_dev_powerdown.c` | MCU firmware: enumerate, observe power-down (quiet bus), verify recovery bus reset + re-enumeration |
| `caliptra_ss_usb_hs_dev_powerdown.yml` | Simulation run config |
