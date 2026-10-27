# Dual-Device High-Speed Bulk Loopback Test

**Testcase:** `caliptra_ss_usb_dual_device_hs_bulk_loopback`

## Overview

Interrupt-driven test that exercises BOTH embedded device controllers of the
compound USB IP (IP_3511) at the same time, behind the on-chip 2-port hub, each
performing an independent 64-byte EP1 bulk OUT-to-IN loopback in parallel:

- **USBDC0 (device0)** - CSR `0x2000_0000`, MEM `0x3000_0000`, PIC vector 3.
- **USBDC1 (device1)** - CSR `0x2000_2000`, MEM `0x3001_0000`, PIC vector 6.

## Interrupt Topology (Option A: no RTL change)

USBDC0's interrupt (`cptra_ss_usb_dev0_irq_o`) is wired to
`cptra_ss_mcu_ext_int[3]` in `caliptra_ss_top.sv` and serviced on VeeR PIC
vector 3 (`service_usb_intr`). USBDC1's interrupt
(`cptra_ss_usb_dev1_irq_o`, from
`caliptra_ss_dut.usb_core_i.dev1_usb_irq`) is NOT routed to the PIC in RTL.
Instead the **testbench** loops the top-level output back onto
`cptra_ss_mcu_ext_int[6]` (`VEER_INTR_VEC_USB_DEV1`) and the MCU services it on
PIC vector 6 (`service_usb_dev1_intr`). Both the TB loopback and the matching
firmware behaviour are gated by the compile define
`USB_HUB_COMPOUND_DEV1_IRQ`, which the yml passes to BOTH the RTL compile and
the firmware `BUILD_CFLAGS`.

The two PIC vectors are configured at EQUAL priority (both 7, see
`caliptra_ss_defines.h`: `CSS_MCU0_VEER_INTR_PRIO_USB_DEV1 = 7`), so the two
controllers' interrupts serialize rather than preempt one another.

## Dual-Aperture Firmware

This is a single dual-device image. It MUST NOT be built with
`-DUSB_DEV_SEL=1` (that would compile-time pin the shared USB library to one
controller). The shared library (`libs/usb/usb.c`) carries a runtime
active-device context: `usb_select_device(0|1)` retargets every CSR/MEM access
and keeps per-device shadow state (device address, current configuration,
remote-wakeup, EP0 IN pending) in private arrays so the two controllers do not
corrupt each other's enumeration state. The firmware calls
`usb_select_device()` around each device's bring-up and per-iteration
servicing.

## Operation

1. `boot_mcu()`, then bring up BOTH controllers:
   `usb_select_device(0); boot_usb_core_hub();` then
   `usb_select_device(1); boot_usb_core_hub();` (HUB_EN is set once; the second
   call's re-write is a harmless idempotent edge while HUB_CONNECT is still
   clear).
2. `init_usb_interrupts()` enables PIC vectors 3 and 6 (vector 6 only compiled
   in under `USB_HUB_COMPOUND_DEV1_IRQ`).
3. `usb_hub_connect()` asserts HUB_CONNECT so the host can enumerate the hub.
4. The VIP host enumerates the hub (@address 1), brings up downstream ports 1
   and 2, and enumerates USBDC0 and USBDC1 (both @address 2 behind their
   respective ports). Firmware drains the ISR mailbox
   (`mcu_intr_rcv.usb` / `mcu_intr_rcv.usb_dev1`), servicing EP0 SETUP/control
   transfers for each controller via `usb_select_device()` +
   `usb_handle_control_transfer()`.
5. Once a controller reaches the Configured state, firmware arms its EP1 OUT
   (64 bytes) and enables its EP1OUT interrupt. On the EP1 OUT completion
   interrupt it copies the 64 received bytes from the EP1 OUT buffer
   (`MEM+0x200`) to the EP1 IN buffer (`MEM+0x240`) and arms EP1 IN. The
   loopback for that controller is DONE once its EP1 IN entry's Active bit
   clears.
6. The test PASSES once BOTH controllers have completed their EP1 loopback.

## What Is Verified

- Simultaneous hub-aware enumeration of USBDC0 (port 1) and USBDC1 (port 2) in
  HS mode.
- Dual-aperture firmware servicing both controllers from a single image via the
  runtime active-device context.
- Independent, parallel EP1 64-byte bulk OUT->IN loopback on both controllers.
- Interrupt delivery on BOTH PIC vectors (3 for dev0, 6 for the TB-looped dev1
  IRQ), with equal-priority serialization.
- End-to-end 64-byte data integrity on each controller (checked host-side).

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_dual_device_hs_bulk_loopback_sequence.svh` | SVT VIP: enumerate hub + USBDC0 (port 1) + USBDC1 (port 2), bulk OUT+IN loopback on both |
| `caliptra_ss_usb_dual_device_hs_bulk_loopback_test.svh` | UVM test class (HS, both downstream ports) |
| `caliptra_ss_usb_dual_device_hs_bulk_loopback.c` | IRQ-driven dual-device MCU firmware |
| `caliptra_ss_usb_dual_device_hs_bulk_loopback.yml` | Simulation run config (`-DUSB_HUB_COMPOUND_DEV1_IRQ`) |
