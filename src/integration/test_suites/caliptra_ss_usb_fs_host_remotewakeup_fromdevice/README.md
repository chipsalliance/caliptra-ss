# caliptra_ss_usb_fs_host_remotewakeup_fromdevice

Device-initiated remote wakeup at full speed, on the on-chip
`usb_hub_composite_device` IP (2-port hub with embedded device controllers).

This is the only USB test in this repository where the DEVICE *starts* the
resume. The `*_global_suspend_L2` family stops SOF and then has the HOST drive
resume K unprompted; here the MCU firmware drives resume K upstream first, and
the host only completes the handshake afterwards.

## The mechanism: device-initiated, host-completed

Remote wakeup is a two-party handshake (USB 2.0 section 7.1.7.7), and confusing
it for a one-shot signal is what made the earlier revisions of this test wrong in
two different ways:

- **Device half.** The firmware writes DEVCMDSTAT with DSUS driven to 0 while
  suspended, which sets `usbreg_remotewakeup`, and the peripheral engine drives
  resume K on the upstream D+/D- pair for `T_3ms` (3.072 ms nominal, 3.089 ms
  measured). *That* is the remote wakeup. It is the DUT feature under test and
  only the device can produce it. The device is not asking to be woken; it is
  waking the host.
- **Host half.** The device cannot finish the resume by itself. The host must
  take over resume signalling within 1 ms and terminate it with a low-speed EOP,
  i.e. an SE0, and only the upstream side can drive an SE0. The RTL encodes
  exactly that contract: `usb_pie.m.vhdl` `BUS_EVENT_SW_WAKEUP_3` exits **only**
  on `ls_filt = LINESTATE_SE0`, with no timer and no other arc, and is excluded
  from `timer_bus_event_run`. A device left to itself parks there forever, never
  returns to `BUS_EVENT_FS_IDLE`, and can never answer post-resume traffic.

So the sequence does drive `svt_usb_link_service_clear_suspend_sequence`, but
strictly **after** the device's K has been observed. That is the host
*completing* a handshake the device started, not the host initiating anything.
The original author's objection - that a host-driven K ends the suspend whether
or not the device ever woke - was valid only for an *unconditional, early*
`clear_suspend`, and the resolution is ordering, not omission. It also cannot
forge the verdict: the check requires the DUT to assert its own `TXValid`, which
a host-driven K does not do.


## What it does

Firmware (`caliptra_ss_usb_fs_host_remotewakeup_fromdevice.c`):

1. `boot_mcu()`, `boot_usb_core_fs()` (FS bring-up + HUB_EN + hub descriptor RAM).
2. `init_usb_interrupts()` (not `init_interrupts()` - see the source comment).
3. `usb_hub_connect()` - second phase of the two-phase hub bring-up. Until
   HUB_CONNECT is set the host sees nothing at all.
4. `usb_allow_clock_stop()` - clears `DEVCMDSTAT.FORCE_NEEDCLK`. Mandatory: while
   FORCE_NEEDCLK is set, `usbreg_pll_on` holds the compound-structure clock on,
   `clk_off_counter` is reloaded every clock instead of counting down, and
   `utmi_suspendm` can never fall - so the controller never reports DSUS and
   there is no suspended state from which to request a wakeup.
5. Poll `USB_DEV_DEVCMDSTAT`, serving EP0 from the ISR mailbox. On the first
   `DSUS_C` with `DSUS` set, record the suspend; after
   `USB_WAKEUP_ARM_DELAY_POLLS` more polls call `usb_request_remote_wakeup()`.
   On the `DSUS_C` edge with `DSUS` clear, record the resume.
6. Keep serving EP0 for `USB_POST_RESUME_GRACE_POLLS`, then halt.

Sequence (`caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence.svh`):

1. Link ENABLED, then SOF, then settle (link-first ordering is deliberate).
2. Hub-aware enumeration A+B+C: hub at address 1, USBDC0 at address 2.
3. Arm both DUT-side checkers (`usb_suspend_stimulus_armed`, shared by the
   suspend/resume checker and the device-wakeup checker).
4. Fork the informational VIP-side wakeup sampler, then SOF off. The sampler
   starts *before* the stimulus because the DUT drives K on its own schedule;
   sampling for it only after the other waits have completed misses it.
5. Wait for the DUT to enter suspend (`usb_dut_suspend_seen`). The gate is the
   DUT event, never the VIP link state - the VIP state is logged for
   information only.
6. Wait for the DEVICE half: `usb_dut_wakeup_k_seen`, triggered by
   `caliptra_ss_usb_device_wakeup_checker` once the DUT has held UTMI `TXValid`
   with `linestate = K` for its minimum hold. No `uvm_error` is raised here on
   timeout - the checker owns that verdict as `CHK_DEVICE_WAKEUP_K`, and it can
   additionally distinguish "never drove K" from "drove K too briefly".
7. Drive the HOST half, in this order and only after step 6:
   `svt_usb_link_service_clear_suspend_sequence` (host takes over the resume and
   terminates it with the low-speed EOP that `BUS_EVENT_SW_WAKEUP_3` is waiting
   for), then restart SOF so the VIP link does not fall straight back into
   suspend.
8. Wait for `usb_dut_resume_seen`, then settle for `POST_RESUME_SETTLE` (3.5 ms,
   sized to cover `T_3ms` of K plus `T_TxENDDELAY` plus the EOP).
9. `GetDescriptor(Device)` to USBDC0 must return a well-formed 18-byte device
   descriptor. Skipped if the device was never seen driving K, so the failure is
   reported once, by `CHK_DEVICE_WAKEUP_K`.
10. Close the checker observation window (`usb_suspend_resume_obs_window_done`).
    Mandatory: neither checker evaluates without it.


## Why this test was rewritten

The previous collateral could not fail for the right reason, and was disabled
(the `include lines in `caliptra_ss_usb_test_pkg.sv` were commented out).

Sequence side: the flow was `suspend -> #5us -> resume_sequence`. The wait was a
fixed delay and the host resume was unconditional, so the outcome was identical
whether or not the device ever drove K. The file contained no `uvm_error` at
all. It also extended plain `uvm_sequence` and hand-rolled its own objections
and agent casts instead of using `caliptra_ss_usb_base_sequence`.

Firmware side: it used `boot_usb_core()` and the legacy `SOC_USBHSD_*` register
base, never called `usb_hub_connect()`, and triggered the "wakeup" with

```c
lsu_write_32(SOC_USBHSD_DEVCMDSTAT,
             lsu_read_32(SOC_USBHSD_DEVCMDSTAT) | DSUS_C_MASK | DRES_C_MASK);
```

That can never work. Per `usb_reg_if.m.vhdl` the wakeup command is a write to
DEVCMDSTAT with **bit 17 (DSUS) driven to 0** while suspended:

```vhdl
if reg_wdata(17) = '0' and reg_dev_suspend = '1' then
  usbreg_remotewakeup <= '1';
end if;
```

A read-modify-write that ORs bits reads DSUS back as 1 while suspended and
therefore writes bit 17 as 1, so the condition is never met.
`usb_request_remote_wakeup()` in `libs/usb/usb.c` performs the correct masked
write (and masks off SETUP / DCON_C / DRES_C so pending events are not lost).

## Scope and limitations

- The hub does not enforce `SetFeature(DEVICE_REMOTE_WAKEUP)`:
  `ep0_remote_wake_enabled` is unconnected in the hub application code, so the
  permission gate cannot be tested. The test exercises the wakeup mechanism, not
  the enable policy.
- Verdict ownership is split across two testbench-scope checkers, and the
  sequence itself owns only the post-resume traffic check:
  - `caliptra_ss_usb_device_wakeup_checker` / `CHK_DEVICE_WAKEUP_K`
    (`+usb_device_wakeup_check=1`) - the DUT drove resume K upstream, observed as
    UTMI `TXValid` asserted with `linestate = 2'b10` for a sustained minimum.
    This is the central assertion. `TXValid` is a DUT *output*, so nothing the
    host or the VIP does can satisfy it.
  - `caliptra_ss_usb_suspend_resume_checker` / `CHK_SUSPEND_SEEN`,
    `CHK_RESUME_SEEN` (`+usb_suspend_resume_check=1`) - the SuspendM edges.
    Note `CHK_RESUME_SEEN` is *not* resume evidence: SuspendM rises on the raw
    wakeup request via `clear_ulpi_req_low_power_mode`, and in the measured run
    it fired 2.8 us *before* the firmware's request. It scores the PHY leaving
    low power, nothing more.

  All of this depends on the sequence triggering the observation window at the
  end - without it neither checker evaluates and the test reports PASSED
  regardless of DUT behaviour.
- `svt_usb_status::device_remote_wakeup_in_progress` is **logged, not checked.**
  It was measured staying 0 through a full, correct, 3.089 ms device K. The most
  probable reason is that the VIP only latches it once it observes a *complete*
  device resume, including the host takeover it expects to perform itself, so the
  device half alone can never satisfy it. Used as a verdict it produced a false
  FAIL on a working DUT. See
  `docs/usb_remote_wakeup_selfclear_race_report.md` sections 2A.4, 7.4 and 7.5.

- Timer build dependency: the sequence's `SUSPEND_DWELL` ceiling (2 ms) assumes
  `G_SIM_CHIRP_TIMERS=1`, which is how `caliptra_ss_top_tb` elaborates the DUT.
  At full speed that selects `T_SUSPEND_DET_SIM_FS = 1100 us`
  (`usb_pie.m.vhdl:508`); the 200 us figure quoted in earlier revisions of this
  README is the HS constant `T_SUSPEND_DET_SIM_HS` and does not apply here. The
  DUT was measured entering suspend 1509 us after SOF-off, so the 2 ms ceiling
  has only about 490 us of margin and must not be reduced. Against a
  `G_SIM_CHIRP_TIMERS=0` build the spec value is 3.072 ms and the ceiling must
  be raised first.
- `tinactivity` is a correctness constraint here, not a performance knob. The
  VIP only reports `device_remote_wakeup_in_progress` if its own link is already
  SUSPENDED when the upstream K arrives, so `cfg.host_cfg.tinactivity` must
  expire BEFORE the DUT's suspend-detect timer: above the 1 ms FS SOF period (or
  the link would suspend in the normal gap between two SOFs) and below the
  ~1500 us DUT suspend latency. The test class uses 1.2 ms. Getting this wrong
  produced a reported wakeup failure while the DUT was in fact correct, so the
  sequence now also latches whether the VIP link was ever seen SUSPENDED and
  reports that case explicitly as a test-configuration fault rather than a DUT
  defect.

## Related

- `caliptra_ss_usb_fs_dev_global_suspend_L2` - host-driven resume, same suspend
  stimulus. The pattern this test is built on.
- `caliptra_ss_usb_hs_dev_hub_port_suspend` - per-port selective suspend, and
  `docs/usb_hub_port_suspend_not_wired_report.md` for why it cannot check
  actuation.
- `docs/usb_remote_wakeup_debug.md` - FORCE_NEEDCLK / clk_off_counter analysis.

File contains AI-generated response based on internal company sources
