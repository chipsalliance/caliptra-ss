# High-Speed Device Suspend/Resume Sanity Test

**Testcase:** `caliptra_ss_usb_hs_dev_sanity_suspend`

## Naming note

Renamed from `caliptra_ss_usb_hs_dev_remote_wakeup`. The scenario is entirely
host-driven: the host stops SOF to suspend the link and then drives the resume
K-state itself, so the device never initiates a wakeup and the old name
described something this test does not do. Device-initiated remote wakeup is
covered by `caliptra_ss_usb_hs_host_remotewakeup_fromdevice` (HS) and
`caliptra_ss_usb_fs_host_remotewakeup_fromdevice` (FS).

## Overview

Verifies HS device suspend and resume signaling on the DUT UTMI `SuspendM`
output. The firmware also traces `DEVCMDSTAT.DSUS_C`, but only as a diagnostic -
see "Scope and Limitations".

## Operation

The MCU firmware performs the two-phase hub bring-up required by the
hub-composite IP: `boot_usb_core_hub()` sets `HUB_CTRL.HUB_EN`, then
`usb_hub_connect()` sets `HUB_CONNECT`. Only after `HUB_CONNECT` does the hub
present itself on the bus, so the host sees connect / reset / HS chirp and the
VIP link reaches `ENABLED`. The firmware then clears `FORCE_NEEDCLK` with
`usb_allow_clock_stop()` so the UTMI clock can actually stop and `SuspendM` can
fall.

The VIP host runs SOF, stops it to drive suspend, waits for the DUT to enter
suspend, drives resume K-state with
`svt_usb_link_service_clear_suspend_sequence`, restarts SOF and waits for the
DUT to leave suspend. The firmware logs both `DSUS_C` events and halts.

## What Is Verified

The verdict is entirely DUT-side, in `caliptra_ss_usb_suspend_resume_checker`
(enabled by `+usb_suspend_resume_check=1` in both the `.mk` and the `.yml`):

- `CHK_SUSPEND_SEEN` - the DUT drives UTMI `SuspendM` low, i.e. the device
  controller entered suspend.
- `CHK_RESUME_SEEN` - having suspended, it drives `SuspendM` high again after
  the host resume. Skipped, with a message, if `CHK_SUSPEND_SEEN` failed.

Both are evaluated only when the sequence triggers
`usb_suspend_resume_obs_window_done` at the end of step 10.

The sequence additionally `uvm_error`s if the VIP upstream link does not reach
`SUSPENDED` after SOF off, or `ENABLED` again after the resume. Those are
host-side observations, not DUT checks.

## Scope and Limitations

Read these before trusting a pass.

- **`DEVCMDSTAT.DSUS_C` is diagnostic only, and zero is the expected count.**
  The firmware prints every suspend-change event it sees and then prints the
  total, but nothing checks it. An earlier revision required two events and
  printed `FAIL` otherwise; that check can never pass on this IP and was
  removed. Measured from the FSDB, window 1080-1145 us:

  | Signal | Behaviour |
  | --- | --- |
  | `PIE_SUSPEND` | 0 -> 1 at 1083628 ns, 1 -> 0 at 1141116 ns (57.5 us) |
  | `utmi_suspendm_o` | 1 -> 0 at 1087845 ns, 0 -> 1 at 1137845 ns |
  | `USB_REG_IF_1 REG_DEV_SUSPEND` | flat 0, zero value changes |
  | `USB_REG_IF_1 REG_DEV_SUSPEND_CHANGE` | flat 0, zero value changes |

  The PIE really did suspend; USBDC0's register block was never told. In
  `usb_reg_if.m.vhdl`, `DEVCMDSTAT.DSUS` is a direct assign of that instance's
  `sync_suspend` (line 196) and `DSUS_C` is set only on a change of it (lines
  836-840), so with `sync_suspend` flat 0 there is no edge to latch.

  The cause is architectural: **the on-chip hub does not propagate upstream
  global suspend down to its downstream port.** See the same note in
  `caliptra_ss_usb_hs_dev_global_suspend_L2/README.md`, which also keeps its
  `DSUS_C` prints diagnostic, and
  `docs/usb/usb_hub_port_suspend_not_wired_report.md` in the accessories repo,
  where per-port suspend being status-only is a designer-accepted deviation.

- **`SuspendM` is a weaker observable than its name suggests.**
  `docs/usb/usb_l1_suspendm_observability_report.md` shows the pin is driven by
  the compound wrapper's clock-gating logic, not by the PIE suspend state, and
  lags the PIE by the `clk_off_counter` hold (~4.2 us here). The stronger
  observable is `PIE_SUSPEND`, which this test measured behaving correctly for
  57.5 us. Wiring that into the shared checker would strengthen the verdict for
  this and ~9 other tests, and has not been done.

- **A minimum suspend hold is mandatory in the stimulus.** The checker fires
  `usb_dut_suspend_seen` the instant `SuspendM` falls, and the resume costs no
  simulation time, so without `MIN_SUSPEND_HOLD` the device suspends and
  resumes in the same time step - one measured run produced a **1 ps** suspend
  that the checker still scored as PASSED. The checker has no minimum-hold
  requirement of its own.

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev_sanity_suspend_sequence.svh` | SVT VIP HS suspend/resume sequence; arms the DUT checker and closes its observation window |
| `caliptra_ss_usb_hs_dev_sanity_suspend_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_dev_sanity_suspend.c` | MCU firmware: hub bring-up and DSUS_C diagnostic monitoring |
| `caliptra_ss_usb_hs_dev_sanity_suspend.mk` | Adds `+usb_suspend_resume_check=1` |
| `caliptra_ss_usb_hs_dev_sanity_suspend.yml` | Simulation run config |

## History

An earlier revision of the firmware omitted `usb_hub_connect()`, so the link
could never reach `ENABLED` and the test hung with zero UVM_ERROR. See
`docs/handover/claude_md/34_usb_hs_dev_sanity_suspend_hub_connect.md` in the
accessories repo.

# File contains AI-generated response based on internal company sources
