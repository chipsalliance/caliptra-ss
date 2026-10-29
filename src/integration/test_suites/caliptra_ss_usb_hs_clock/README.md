# High-Speed (HS) Link Test

**Testcase:** `caliptra_ss_usb_hs_clock`

## Overview

HS counterpart of `caliptra_ss_usb_fs_clock`. Verifies that the USB device
controller behind the compound hub links up and runs at High Speed
(480 Mbit/s). This is a passive link-observer test: the host performs the HS
chirp/link-up handshake, starts SOF generation, and holds an observation
window; no enumeration control transfers are issued.

Unlike the FS variant, this test does NOT enable the FS line-speed checker
(`caliptra_ss_usb_fs_speed_checker.sv`), which is specific to FS and would
correctly fail on an HS link. The HS link speed is exercised implicitly by the
VIP HS chirp handshake.

## Operation

1. The UVM test leaves `high_speed_capable = 1` (default) so the VIP host
   drives the HS chirp during bus reset and both sides settle at High Speed.
2. MCU firmware calls `boot_usb_core()`, which
   - performs hub bring-up phase 1 (programs and validates the HUB descriptor
     RAM, sets `HUB_EN`), and
   - programs USBDC0 for normal HS operation (no `DEVCMDSTAT.PFSC`, so the
     device controller participates in the HS chirp handshake).
3. Firmware calls `usb_hub_connect()` (phase 2, `HUB_CONNECT`) once USBDC0 is
   fully programmed, so the upstream host can see the hub.
4. The host sequence waits for the link to reach `ENABLED` (bounded by
   `link_up_timeout_us`, which raises a `uvm_error` on expiry), starts SOF
   generation, and holds an observation window.
5. Firmware idles servicing bus resets, then halts via `csr_write_mpmc_halt()`.

## What Is Verified

- Two-phase hub bring-up results in the host performing HS chirp and the link
  reaching `ENABLED` within `link_up_timeout_us` (host sequence).
- HS chirp sequence completes at 480 Mbit/s.
- Firmware reaches `csr_write_mpmc_halt()` within the MCU-halt timeout
  (`caliptra_ss_usb_base_test`), and no `UVM_ERROR`/`UVM_FATAL` was reported.

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_clock_sequence.svh` | SVT VIP host sequence (HS mode, bounded link-up wait) |
| `caliptra_ss_usb_hs_clock_test.svh` | UVM test class (`high_speed_capable = 1`) |
| `caliptra_ss_usb_hs_clock.c` | MCU firmware for HS link bring-up |
| `caliptra_ss_usb_hs_clock.yml` | Simulation run config |

## Run

```
cd $CALIPTRA_WORKSPACE
source caliptra_setup_env.csh
source my_local_env.csh
./run_caliptra_test.py -test caliptra_ss_usb_hs_clock
grep -nE "TESTCASE (PASSED|FAILED)|UVM_ERROR" scratch/vcs_sim.log
```

> Ported with acc from `caliptra_ss_usb_fs_clock` (HS counterpart).
