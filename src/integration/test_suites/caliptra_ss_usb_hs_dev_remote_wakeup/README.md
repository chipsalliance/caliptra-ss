# High-Speed Device Suspend / Resume Test

**Testcase:** `caliptra_ss_usb_hs_dev_remote_wakeup`

## Overview

Brings the upstream USB 2.0 link up at High Speed, suspends it from the host
side (SOF off), holds it suspended, then resumes it from the host side and
checks that the link returns to `ENABLED`. In parallel the MCU firmware polls
`DEVCMDSTAT` on USBDC0 and logs any `DSUS_C` (suspend-change) events it sees.

## Topology (hub-composite IP)

The DUT is the hub-composite USB IP (`ip_xxx_3511_hs_mem_compound_wrapper`): an
on-chip 2-port USB hub with an embedded downstream device controller, USBDC0,
which is the device the MCU owns. USBDC0 is no longer a device directly on the
bus; it sits *behind* the hub.

Two consequences for this test:

1. **Two-phase bring-up is mandatory.** `boot_usb_core()` programs USBDC0 and,
   internally via `usb_hub_init_and_connect()`, loads and validates the hub
   descriptor RAM and sets `HUB_EN`. The test's `main()` must then call
   `usb_hub_connect()` to set `HUB_CONNECT` once USBDC0 is fully programmed.
   Only after `HUB_CONNECT` does the host see a connect, drive bus reset and HS
   chirp, and reach `ENABLED`. Without it the upstream link never comes up and
   there is nothing to suspend.
2. **Register addresses moved.** The legacy `SOC_USBHSD_*` addresses (base
   `0x2000_0000`) now decode to the hub's small register bank. USBDC0's
   registers are at `USB_DEV0_REG_BASE_ADDR` (`0x2000_1000`), so this test uses
   the `USB_DEV0_*` macros from `libs/usb/usb.h`. The bit-mask macros
   (`USBHSD_DEVCMDSTAT_*_MASK`, `USBHSD_INTSTAT_*_MASK`) are unchanged.

## Operation

Host-side sequence (`caliptra_ss_usb_hs_dev_remote_wakeup_sequence.svh`):

1. Wait for the upstream link to reach `ENABLED`.
2. Start SOF generation.
3. Settle (`LINK_SETTLE_DELAY`).
4. Suspend the link with SOF off.
5. Poll until the VIP link state is `SUSPENDED` (else `uvm_error`).
5b. Arm the DUT-side checker by triggering `usb_suspend_stimulus_armed`. This
    is mandatory. Out of reset the DUT holds `SuspendM` low by design (PHY
    clocks gated) and raises it inside `boot_usb_core`, so a checker watching
    from time zero would score that boot-time low-then-high as a complete
    suspend/resume cycle and report a false pass. Arming here, after `sof_off`
    and after the VIP link has confirmed `SUSPENDED`, is the earliest point at
    which a `SuspendM` change is attributable to this stimulus.
6. Wait for the DUT to enter suspend, i.e. for the checker to trigger

   `usb_dut_suspend_seen`, bounded by `SUSPEND_DWELL` as a timeout ceiling.
7. Drive resume K-state with `svt_usb_link_service_clear_suspend_sequence`.
8. Restart SOF so the link is not re-suspended by the keepalive timeout.
9. Poll until the link is `ENABLED` again (else `uvm_error`), then wait for the
   DUT to leave suspend (`usb_dut_resume_seen`), bounded by `RESUME_WAIT_MAX`.
10. Short observation window (`POST_RESUME_OBS`), then trigger
    `usb_suspend_resume_obs_window_done` so the checker evaluates its checks.


MCU firmware (`caliptra_ss_usb_hs_dev_remote_wakeup.c`) runs a polling loop that
services EP0 SETUP/IN/OUT, and on `DEVCMDSTAT.DSUS_C` clears the bit
(write-1-to-clear) and prints `MCU: Suspend change event <n> DEVCMDSTAT=0x...`.

## What Is Actually Checked

Host side, in the sequence:

- The VIP link reaches `SUSPENDED` after SOF off, within the poll ceiling.
- The VIP link returns to `ENABLED` after host resume, within the poll ceiling.

DUT side, in `caliptra_ss_usb_suspend_resume_checker.sv` (enabled by
`+usb_suspend_resume_check=1`, which the yml passes). It watches the DUT UTMI
`SuspendM` output, which is active low:

- `CHK_SUSPEND_SEEN` - the DUT must drive `SuspendM` low, i.e. the device
  controller behind the hub really did enter suspend.
- `CHK_RESUME_SEEN` - having suspended, the DUT must drive `SuspendM` high
  again after the host resume. Skipped, with a message, if `CHK_SUSPEND_SEEN`
  already failed.

Both are evaluated when the sequence triggers
`usb_suspend_resume_obs_window_done`, and failures are reported with
`uvm_report_error` so they reach the `TESTCASE FAILED` verdict.


## Scope and Limitations

Read these before trusting a pass.

- **The name is misleading.** Resume here is **host-initiated**
  (`clear_suspend`). The firmware never signals remote wakeup upstream: it does
  not write `DEVCMDSTAT.DSUS`, and `sys_dev_wakeup_n` is untouched. Device-side
  remote-wakeup initiation is *not* covered. A separate
  `caliptra_ss_usb_host_remotewakeup` test exists in the same family.
- **The firmware-side `DSUS_C` prints are still not checked by anything.** They
  remain diagnostic only. The DUT-side evidence that is checked is the UTMI
  `SuspendM` pin, not the firmware's view of `DEVCMDSTAT`.
- **Open question after the hub migration:** a USB hub is not required to
  propagate upstream suspend down to a downstream port. Per-port suspend is
  normally requested explicitly with `SetPortFeature(PORT_SUSPEND)` addressed
  to the hub, so USBDC0 may not see suspend at all in this topology. That is
  now an honest question rather than a silent pass: if the hub does not
  propagate it, `CHK_SUSPEND_SEEN` fails and says so. If a run shows that
  failure, the options are to add a `SetPortFeature(PORT_SUSPEND)` step to the
  stimulus, or to narrow the documented scope to the upstream link only and
  drop the plusarg.


## Runtime

Two changes reduce the simulated time of this test. No wall-clock figures are
quoted below because no measured baseline run for this test has been recorded;
the numbers are sums of the timer values in the RTL, the VIP configuration and
the sequence.

**1. The dwells became ceilings.** `SUSPEND_DWELL` (2 ms) and `RESUME_WAIT_MAX`
(500 us) used to be unconditional delays. The sequence now waits on
`usb_dut_suspend_seen` / `usb_dut_resume_seen` from the checker and continues as
soon as the DUT reacts, so in the passing case neither ceiling is paid at all.
The dwell ends because the DUT responded, not because a timer tuned on the
legacy single-device topology expired.

**2. The DUT suspend-detection timer is sim-scaled.** The device decides the bus
is suspended from absence of activity, using `T_SUSPEND_DET` in
`usb_pie.m.vhdl`. That constant now follows the existing `sel_nat` /
`G_SIM_CHIRP_TIMERS` pattern already used for the chirp timers:

| | value | note |
|---|---|---|
| `T_SUSPEND_DET_SPEC` | 3.072 ms | spec value, `G_SIM_CHIRP_TIMERS = 0` |
| `T_SUSPEND_DET_SIM` | 200 us | sim value, `G_SIM_CHIRP_TIMERS = 1` |

This testbench elaborates the DUT with `G_SIM_CHIRP_TIMERS(1)` (see
`caliptra_ss_top_tb.sv`), so the sim value applies here.

Adding up the terms on the suspend half - the parts that must elapse before the
DUT can possibly react - gives 500 us `LINK_SETTLE_DELAY`, about 300 us of VIP
inactivity timer, `T_SUSPEND_DET`, and about 100 us of `T_TWTRSTHS`: roughly
4.0 ms with the spec timer, roughly 1.1 ms with the sim timer. That is about a
3.5x to 4x reduction on that half.

**Caveat for spec-timer builds.** With `G_SIM_CHIRP_TIMERS = 0` the DUT needs
3.072 ms to detect suspend, which is longer than the 2 ms `SUSPEND_DWELL`
ceiling. The wait would time out before the DUT could physically react and
`CHK_SUSPEND_SEEN` would fail for a reason that is not a DUT bug. Raise the
ceiling above 3.072 ms before running this test against such a build.

All delays are named `localparam`s at the top of the sequence class, tagged as
either protocol/VIP-bound or empirical margin. `LINK_SETTLE_DELAY` (500 us) is
the largest remaining unconditional delay and is the next candidate for
trimming, guided by timestamps from a passing baseline log.


The two poll bounds (`SUSPEND_POLL_MAX_US`, `ENABLED_POLL_MAX_US`) are timeout
ceilings only; the loops exit as soon as the state is reached and so cost
nothing in the passing case.


## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev_remote_wakeup_sequence.svh` | Host-side suspend / resume sequence |
| `caliptra_ss_usb_hs_dev_remote_wakeup_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_dev_remote_wakeup.c` | MCU firmware: hub connect, EP0 service, DSUS_C logging |
| `caliptra_ss_usb_hs_dev_remote_wakeup.yml` | Simulation run config, including `+usb_suspend_resume_check=1` |
| `../../testbench/caliptra_ss_usb_suspend_resume_checker.sv` | DUT-side checker on UTMI `SuspendM`; owns the pass/fail verdict |


## Running

```
./run_caliptra_test.py -test caliptra_ss_usb_hs_dev_remote_wakeup -sim_dir <dir>
```
