# Dual-Device Full-Speed Bulk Loopback Test

**Testcase:** `caliptra_ss_usb_dual_device_fs_bulk_loopback`

## Overview

Full-speed port of `caliptra_ss_usb_dual_device_hs_bulk_loopback`. It is an
interrupt-driven test that exercises BOTH embedded device controllers of the
compound USB IP (IP_3511) at the same time, behind the on-chip 2-port hub, each
performing an independent 64-byte EP1 bulk OUT-to-IN loopback in parallel, with
the link negotiated at Full Speed (12 Mbit/s) instead of High Speed:

- **USBDC0 (device0)** - CSR `0x2000_0000`, MEM `0x3000_0000`, PIC vector 3,
  hub downstream port 1, USB device address 2.
- **USBDC1 (device1)** - CSR `0x2000_2000`, MEM `0x3001_0000`, PIC vector 6,
  hub downstream port 2, USB device address 3.

## What Makes This Test Full Speed

### Firmware

The only firmware-visible difference from the HS test is the device bring-up
entry point: this test calls `boot_usb_core_fs()` instead of
`boot_usb_core_hub()`. The two are identical except that the FS variant also
sets `DEVCMDSTAT` bit 21 (FORCE_FULLSPEED, the legacy PFSC bit) before
connecting. That suppresses the device-side K-chirp, so the UTMI transmitter is
ready for FS packet exchange immediately after bus reset instead of waiting for
a chirp handshake the host never answers.

FORCE_FULLSPEED is a per-device control, so `boot_usb_core_fs()` must be called
on BOTH controllers; booting only one would leave the other chirping.

### Host VIP configuration

`caliptra_ss_usb_dual_device_fs_bulk_loopback_test.svh` configures the SVT VIP
for FS:

- `high_speed_capable = 0` so the host never offers the HS chirp.
- `speed`, `connected_bus_speed`, `functionality_support` and EVERY
  `endpoint_cfg[].speed` / `max_packet_size` re-stamped to the FS constants.
  Leaving an endpoint at HS on an FS link makes the VIP emit HS-sized DATA
  packets that the FS link state machine cannot carry, which trips
  `tend_to_end_delay_check` on the first control transfer.
- `tddis` = 2 ms, `tend_to_end_delay_fs` = 2 ms, `tinactivity` = 5 ms - all
  widened past the 1 ms FS frame period, since tokens are only scheduled on SOF
  boundaries and the scaledown defaults are microseconds.
- `drive_reset_time` = 150 us, because with `high_speed_capable = 0` the VIP
  otherwise transitions DISCONNECTED -> ENABLED without ever driving SE0 and
  the DUT never enters DEFAULT state.
- `allow_aligned_transfer_without_zero_length = 1` on the EP1 BULK OUT entry.
  At FS the bulk max packet is 64, so the 64-byte payload is exactly aligned
  and the VIP would otherwise append a ZLP that the firmware NAKs. At HS (max
  packet 512) the same transfer was a short packet and this was cosmetic.

The host sequence also widens the firmware-turnaround delays from 20 us (HS) to
200 us, for the same SOF-boundary reason.

### FS line-speed checking

The run is not trusted to be FS just because it was configured that way. Both
the yml and `caliptra_ss_usb_dual_device_fs_bulk_loopback.mk` pass
`+usb_fs_speed_check=1`, which arms `caliptra_ss_usb_fs_speed_checker.sv`
(instantiated in `caliptra_ss_top_tb.sv`, inert without the plusarg):

| Check | Verifies |
|-------|----------|
| `CHK_XCVR_FS` | `XcvrSelect = 1` and `TermSelect = 1` on the first packet (both would be 0 had the chirp reached HS) |
| `CHK_RATE_FS` | measured RXValid-to-RXValid byte period is ~667 ns (12 Mbit/s), not ~17 ns (480 Mbit/s) |
| `CHK_SAW_TRAFFIC` | completeness guard: fails if no packet was ever seen, or too few samples were collected to confirm the rate |

`CHK_SAW_TRAFFIC` is released by the global `uvm_event`
`usb_fs_obs_window_done`, which the sequence triggers once both loopbacks have
completed (and also on the link-up timeout path, so an aborted run cannot pass
by leaving the check unevaluated).

`CHK_SOF_PERIOD` (`+usb_fs_sof_check`) is deliberately NOT enabled: it needs
milliseconds of SOF observation that this test does not run long enough to
provide.

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

1. `boot_mcu()`, then bring up BOTH controllers in FS-only mode:
   `usb_select_device(0); boot_usb_core_fs();` then
   `usb_select_device(1); boot_usb_core_fs();` (HUB_EN is set once; the second
   call's re-write is a harmless idempotent edge while HUB_CONNECT is still
   clear).
2. `init_usb_interrupts()` enables PIC vectors 3 and 6 (vector 6 only compiled
   in under `USB_HUB_COMPOUND_DEV1_IRQ`).
3. `usb_hub_connect()` asserts HUB_CONNECT so the host can enumerate the hub.
4. The VIP host enumerates the hub (@address 1), brings up downstream ports 1
   and 2, and enumerates USBDC0 (@address 2) and USBDC1 (@address 3) behind
   their respective ports. Because the VIP models a single remote device, the
   sequence re-anchors onto one controller at a time by mutating
   `remote_device_cfg[0].device_address` and calling `reconfigure()`. Firmware
   drains the ISR mailbox (`mcu_intr_rcv.usb` / `mcu_intr_rcv.usb_dev1`),
   servicing EP0 SETUP/control transfers for each controller via
   `usb_select_device()` + `usb_handle_control_transfer()`.
5. Once a controller reaches the Configured state, firmware arms its EP1 OUT
   (64 bytes) and enables its EP1OUT interrupt. On the EP1 OUT completion
   interrupt it copies the 64 received bytes from the EP1 OUT buffer
   (`MEM+0x200`) to the EP1 IN buffer (`MEM+0x240`) and arms EP1 IN. The
   loopback for that controller is DONE once its EP1 IN entry's Active bit
   clears.
6. The test PASSES once BOTH controllers have completed their EP1 loopback,
   the host-side data comparison matches, and the FS speed checker reports no
   violations.

## What Is Verified

- Simultaneous hub-aware enumeration of USBDC0 (port 1, address 2) and USBDC1
  (port 2, address 3) in FS mode.
- That the link really is Full Speed and not High Speed, via the UTMI
  `XcvrSelect`/`TermSelect` and byte-rate checks.
- `boot_usb_core_fs()` / FORCE_FULLSPEED bring-up on both controllers with no
  chirp handshake.
- Dual-aperture firmware servicing both controllers from a single image via the
  runtime active-device context.
- Independent, parallel EP1 64-byte bulk OUT->IN loopback on both controllers,
  including the max-packet-aligned (no-ZLP) FS bulk OUT case.
- Interrupt delivery on BOTH PIC vectors (3 for dev0, 6 for the TB-looped dev1
  IRQ), with equal-priority serialization.
- End-to-end 64-byte data integrity on each controller (checked host-side).

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_dual_device_fs_bulk_loopback_sequence.svh` | SVT VIP: enumerate hub + USBDC0 (port 1) + USBDC1 (port 2), bulk OUT+IN loopback on both, closes the FS speed-check window |
| `caliptra_ss_usb_dual_device_fs_bulk_loopback_test.svh` | UVM test class (FS link + FS endpoint/timing configuration) |
| `caliptra_ss_usb_dual_device_fs_bulk_loopback.c` | IRQ-driven dual-device MCU firmware (`boot_usb_core_fs()` on both controllers) |
| `caliptra_ss_usb_dual_device_fs_bulk_loopback.yml` | Simulation run config (`-DUSB_HUB_COMPOUND_DEV1_IRQ`, `+usb_fs_speed_check=1`) |
| `caliptra_ss_usb_dual_device_fs_bulk_loopback.mk` | Per-test makefile fragment that arms `caliptra_ss_usb_fs_speed_checker.sv` |
