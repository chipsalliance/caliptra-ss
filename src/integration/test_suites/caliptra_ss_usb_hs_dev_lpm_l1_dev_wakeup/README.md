# caliptra_ss_usb_hs_dev_lpm_l1_dev_wakeup

Device-initiated exit from L1 (LPM Sleep) on USBDC0, at High Speed.

This is the **device-driven** counterpart of `caliptra_ss_usb_hs_dev_lpm_l1`.
Entry into L1 is identical in both suites — an EXT + LPM token addressed to
dev0 — and so are the UVM test class, the sequence and the firmware's
event-classification logic. The only difference is **who ends the L1 dwell**:

| Suite | L1 exit driven by | Firmware build | Plusarg |
|---|---|---|---|
| `caliptra_ss_usb_hs_dev_lpm_l1` | host (`svt_usb_link_service_clear_l1suspend_sequence`) | default | none |
| `caliptra_ss_usb_hs_dev_lpm_l1_dev_wakeup` (this) | the device **requests** it; the host then terminates the resume **reactively** (`svt_usb_link_service_remote_wakeup_after_l1suspend_sequence`) | `-DUSB_LPM_DEVICE_INITIATED_EXIT=1` | `+usb_lpm_dev_wakeup=1` `+usb_device_wakeup_check=1` |

The two legs use **different** VIP link-service sequences on purpose. See
"Why not `clear_l1suspend` on this leg" below - it is a measured finding, not a
preference.


## The host is not silent on this leg, and must not be

An earlier version of this suite had the host stay completely quiet here. That
cannot work, and it is worth understanding why before changing anything.

`BUS_EVENT_SW_WAKEUP_3` in `usb_pie.m.vhdl` waits on
`ls_filt = LINESTATE_SE0` and has **no timeout arm**. A device-initiated resume
is a two-party handshake: the device drives K, and the *host* must terminate it
with SE0. With no host response the DUT parks in `SW_WAKEUP_3` forever and the
run hangs. That hang is correct RTL behaviour, not a DUT bug.

So the host does respond — but **reactively**, never on a schedule:

```
firmware doorbell -> DUT drives K on its own UTMI TXValid
  -> caliptra_ss_usb_device_wakeup_checker sees TXValid + linestate=K
     held for K_MIN_HOLD (20 us)
  -> it triggers the global event usb_dut_wakeup_k_seen
  -> ONLY THEN does the sequence drive the host resume (terminating SE0)
```


This ordering is the whole point. The host response is *caused by* the device's
request, so a DUT that never asks for wakeup cannot be rescued by a well-timed
host resume: the event never fires, the takeover is skipped, and the sequence
reports the failure. The checker keys on a DUT **output**, so nothing the host
or the VIP does can forge it.

**Do not replace this with a fixed delay before driving the resume.** A
perfectly-timed host resume would exit L1 and make the run look healthy whether
or not the device ever requested anything, which defeats the test.

`+usb_device_wakeup_check` is therefore mandatory on this leg, not optional
instrumentation: it is the mechanism that detects the request *and* supplies the
`CHK_DEVICE_WAKEUP_K` verdict.

### What counts as "the DUT left L1", and what does not

Measured on hardware, three otherwise-obvious indicators are **unsound** on
this path. The verdict is a **post-resume `GetDescriptor(Device)` to USBDC0**
instead: if the device really completed its own resume it answers traffic, and
it cannot answer while the PIE is parked in `SW_WAKEUP_3`.

| Indicator | Why it does not work |
|---|---|
| `usb_dut_resume_seen` | Gated on `suspend_seen`, which needs a **falling** `SuspendM` edge. In L1 `SuspendM` never drops (checker arms at level 1; no "DUT entered low-power state" line ever appears), so the event is **unfireable** and any test on it is false by construction. An earlier revision used this and produced a false failure on a healthy run. |
| Step 8 `link_usb_20_state == ENABLED` | The **host VIP's** view, and a *level* check not a transition - passes trivially if the VIP never moved to `L1SUSPENDED` in its own view. |
| `DEVCMDSTAT.LPM_SUS` falling | Marks the PIE **entering** the wakeup FSM, not completing it. Observed dropping 14 us *before* the host responded at all. |

Corollary worth chasing separately: because `SuspendM` does not drop in L1,
`CHK_SUSPEND_SEEN` / `CHK_RESUME_SEEN` rest on a false premise for **both**
`lpm_l1` legs.

### Note on the L1 timing budget

The device holds K for only `T_60us` (60 us) and is parked in `SW_WAKEUP_3`
about 90 us after its first K bit (`T_60us` + `T_TxENDDELAY` = 60 + 30 us at
60 MHz). The checker needs 20 us of that before it can report the K at all, so
the window for the host takeover is narrow.

This is much tighter than the L2 analogue
(`caliptra_ss_usb_hs_host_remotewakeup_fromdevice`), where the device drives K
for `T_3ms` and the host has milliseconds to react. The sequence stretches the
host K via `tdrsmdn = HOST_L1_RESUME_K_PS` (200 us) so the terminating SE0
lands inside `SW_WAKEUP_3` rather than before the DUT arrives there, and it logs
the measured takeover latency so a late takeover is visible as a number rather
than as a mystery hang.

**The window has been measured and it is adequate.** The DUT drove K at
504000 ns, the checker published the event at 524000 ns, leaving 40 us of the
60 us K still in flight. An earlier note claiming the L1 K was "too tight for a
sequence-level takeover" was wrong and has been withdrawn.

What *was* too slow was the plumbing: the responder originally sat behind step
6's wait on `usb_dut_suspend_seen`, which L1 never fires, so it burned the full
`L1_DWELL_MAX = 500 us` and the takeover landed at 1001379 ns - 477 us late,
after the K had ended and the MCU had halted. Forking the responder at step 4a
(before the LPM token) brought that to ~0. **Do not move it back inline.**

### Why not `clear_l1suspend` on this leg

The host-driven suite uses `svt_usb_link_service_clear_l1suspend_sequence`.
This suite deliberately does not, because on the device-initiated path that
sequence is a **silent no-op**. Measured, with the responder correctly firing
at 524000 ns:

- `env.host_agent.link_mon.link_svc_trace` contains **exactly one row** for the
  whole run: `USB_20_PORT_START_LPM` at 492066-500998 ns. There is no second
  link command, so no resume was ever issued at the link layer.
- the physical service trace shows the host's last activity as `END_OF_RESUME`
  at 513198 ns - *before* the device K. After 524000 ns the host drives nothing
  at all until 815998 ns.
- the sequence still reported "takeover complete" with a **0.000 ns** latency,
  because `start()` returned immediately. Returning is not the same as acting.

This is **not** the same as the earlier (retracted) claim that
`clear_l1suspend` *hangs* inside `start()`. It does not hang; it completes
without doing any work, because the link is already leaving L1 under the
device's control and `clear_l1suspend` only knows how to *originate* a
host-initiated exit.
`svt_usb_link_service_remote_wakeup_after_l1suspend_sequence` is the VIP's
sequence for the case where the device asked first.

**When triaging the host half, read `link_svc_trace`, not the log text.** Both
sequences log success either way.

**Measured result of that swap: `remote_wakeup_after_l1suspend` leaves
`link_svc_trace` equally empty.** Still one row. So *no* protocol-layer link
service sequence in this VIP terminates a device-initiated L1 resume, and the
`tdrsmdn` stretch has nothing to act on either. Keep this in mind before
spending more time on link-service sequences.

### The host VIP may already be self-resuming

The physical trace shows something the link trace does not: the host drove a
resume of its own at **507198 ns** (`REG_WRITE 04=55`) and ended it at
**513198 ns** (`END_OF_RESUME`) - *before* the checker published the device K at
524000 ns. `DEVCMDSTAT.LPM_SUS` dropped at 509835 ns, i.e. **inside that
window**.

The most likely reading is that the host VIP honours the `HIRD` field from the
LPM token and self-terminates L1 after the negotiated resume duration, without
needing any sequence to ask it to. If that is correct then:

- the DUT's L1 exit is being completed by the VIP's own HIRD-driven resume, not
  by our reactive takeover;
- the device still genuinely requested wakeup (`CHK_DEVICE_WAKEUP_K` keys on a
  DUT output and passes), so the device-side coverage is intact;
- but the *causality* the test is trying to prove - device asks, host answers -
  is not actually being demonstrated, because the host answered on a timer
  derived from `HIRD` before it knew the device had asked.

This needs resolving before the suite can be called complete. Options not yet
evaluated: raise `HIRD` so the host's own resume lands after the device K
rather than before it, or drive the terminating SE0 from the physical layer
where the reactive ordering can be enforced. Do not "fix" it by declaring the
HIRD resume good enough - that is the pre-scheduled resume this suite exists to
avoid.


### Watch out: the verdict can be truncated away

The post-resume traffic check runs *after* the `L1_EXIT_WAIT_MAX` arm, and that
arm always runs to its full ceiling because `usb_dut_resume_seen` is unfireable
here. The MCU halts shortly after it finishes its own L1 logging (~515 us), and
`caliptra_ss_usb_base_test` releases its `run_phase` objection on halt - so the
simulation can end *before* the verdict executes.

That happened at `L1_EXIT_WAIT_MAX = 500 us`: step 8 completed at 534379 ns,
the verdict would have run at 1034379 ns, and the run ended at 990671 ns. The
symptom is **no `PASS` and no `FAILED` line at all** - the log just stops after
a `reconfigure()` dump, which reads like a hang but is a truncation.
`L1_EXIT_WAIT_MAX` is now 100 us for this reason. If you raise it, extend the
MCU's post-test dwell too.


## Why this is a separate suite rather than a mode of the other one

`USB_LPM_DEVICE_INITIATED_EXIT` is a **compile-time** define, and MCU firmware
cannot read UVM plusargs. A single `mcu_program.hex` therefore cannot serve
both legs, so each leg needs its own build recipe and hence its own suite.
Both `.c` files are near-identical by design; only the header comments and the
default of `USB_LPM_DEVICE_INITIATED_EXIT` differ.

The two knobs are a matched pair. A mismatch does not produce a clean error:

- **plusarg without the define** — the firmware never rings the doorbell, so the
  device never drives K, `usb_dut_wakeup_k_seen` never fires and the host
  takeover is correctly skipped. Reported as
  `FAILED at the device half` (see Failure triage below).

- **define without the plusarg** — the sequence takes its *host-driven* branch
  while the firmware also requests wakeup, so two resume sources overlap and the
  log cannot attribute which one woke the link. (Same hazard the
  `caliptra_ss_usb_fs_host_remotewakeup_fromdevice` sequence warns about.)

## How the device actually wakes the link

This is the part worth reading before debugging a failure, because the bit
names are misleading.

`DEVCMDSTAT.LPM_SUS` (bit 19) is **read-only status**, not a control bit. In
`usb_reg_if.m.vhdl`:

```vhdl
reg_dev_lpm_suspend <= sync_lpm_suspend;   -- from the link engine
...
reg_rdata(19)       <= reg_dev_lpm_suspend;  -- read path only
```

There is no write path to it. Firmware cannot clear `LPM_SUS`; seeing it drop
is the link engine *reporting* that L1 was left.

What `usb_request_lpm_remote_wakeup()` does is ring a **doorbell encoded in
that read-only bit position**:

```vhdl
if reg_wdata(19) = '0' and reg_dev_lpm_suspend = '1'
                       and reg_dev_lpm_remote_wake = '1' then
  usbreg_lpmremotewakeup <= '1';
end if;
```

`usbreg_lpmremotewakeup` is a **separate flop**, self-clearing once
`reg_dev_lpm_suspend` returns to 0. On the dev0 instance (`usb_reg_if_1`) it is
wired directly to `hub_port_lpmremotewakeup(0)`, which fans out two ways in
`ip_xxx_3511_hs_mem_compound_structure.a.vhdl`:

1. **Hub bookkeeping** — `usb_app_hw_hub.m.vhdl` clears `hub_port_l1_int(0)`
   and raises `hub_port_l1_change(0)` (the `C_PORT_L1` status bit).
2. **Upstream resume** — the OR-tree at line ~2335:
   ```vhdl
   hub_lpmremotewakeup <= sync_lpm_suspend and
                          sync_lpm_rw      and
                          (hub_epin_enable_buffer                               or
                           (hub_port_enable(0) and hub_port_lpmremotewakeup(0)) or
                           (hub_port_enable(1) and hub_port_lpmremotewakeup(1)));
   ```
   feeds the top-level `usbreg_lpmremotewakeup`, and `usb_pie.m.vhdl` leaves
   `BUS_EVENT_LPM_SUSPEND_L1` on it (`-- DEVICE asserts its own RESUME`),
   driving K for `T_60us` before rejoining the normal wakeup path.

So **no connect/disconnect of a downstream device is needed to wake the hub** —
the OR-tree already admits each enumerated port's own request. The causal order
is the reverse of what the bit name suggests:

```
firmware doorbell write
  -> hub_port_lpmremotewakeup(0) = 1
  -> hub_lpmremotewakeup = 1
  -> usb_pie drives K upstream (T_60us)
  -> link leaves L1
  -> sync_lpm_suspend drops
  -> LPM_SUS reads 0, doorbell flop self-clears
```

Both preconditions the doorbell checks are already met by the shared sequence:
entering L1 sets `dev0_lpm_suspend` (hence `LPM_SUS=1`) because
`hub_port_enable(0)` is set, and the sequence hardcodes `LPM_BREMOTEWAKE=1'b1`,
which arrives as `dev0_lpm_rw` and reads back as `LPM_REWP=1`.

## Expected log signature

**Where to look.** With `+svt_debug_opts` on (the default for this suite) the
sequence's own `USB_LPM_L1_SEQ` messages go to **`svt_debug.transcript`**, not
to `vcs_sim.log`. A run with zero `USB_LPM_L1_SEQ` lines in `vcs_sim.log` is
normal and does **not** mean the sequence was skipped - grep the transcript
before concluding anything about which branch ran.

Firmware side (`mcu_console.log` / `vcs_sim.log`):

```
MCU: L1 ENTRY event 1 DEVCMDSTAT=0x12994882 LPM=0x0 HIRD_HW=0 REWP=1
MCU: L1 remote wakeup requested (wrote DEVCMDSTAT=0x12914882, reads back 0x10994882)
MCU: device-initiated L1 exit driven
MCU: L1 EXIT event 2 DEVCMDSTAT=0x12914882 LPM=0x0
MCU: L1 cycle complete, HIRD_HW seen at entry = 0, REWP = 1
```

`HIRD_HW` is shown as **0** because that is what the hardware actually reports,
even though the sequence requests `HIRD=1` in the LPM token. That mismatch is a
known open item tracked separately; it is not part of the remote-wakeup path
and does not affect the verdict here.

UVM side (`svt_debug.transcript`), in order:

```
CHK_DEVICE_WAKEUP_K: DUT drove resume K upstream (TXValid high, linestate=K) ...
Device half done: the DUT drove resume K upstream on its own UTMI TXValid ...
Host resume takeover complete; terminating SE0 driven <latency> after the
  device-wakeup-K event ...
Device-driven leg: the DUT has already begun its own L1 exit ...
Device half and host takeover both complete ...
Link ENABLED again <n> us after L1 exit.
postL1: issuing GetDescriptor(Device) to USBDC0 ...
Device-initiated L1 exit PASS: ...
```

Note what is **absent**: there is no "DUT left low-power state" line on this
path. `SuspendM` never drops in L1, so the suspend/resume checker cannot fire
(see the unsound-indicator table above) and the sequence does not use it as the
verdict.

### Failure triage

Three outcomes are reported explicitly. Find that line first - and if you find
**none** of them, see "the verdict can be truncated away" above before
assuming a hang.

- `Device-initiated L1 exit FAILED at the device half` — the DUT never drove
  resume K, so the doorbell was never acted on. This is the real device-side
  failure. No host resume was driven, on purpose. Check that
  `+usb_device_wakeup_check` is on, that the firmware was built with
  `-DUSB_LPM_DEVICE_INITIATED_EXIT=1`, and that `LPM_SUS` and `LPM_REWP` were
  both set when the doorbell write was issued.
- `Device-initiated L1 exit FAILED to complete` — the device half worked
  (`CHK_DEVICE_WAKEUP_K` passed) and the host answered, but USBDC0 did not
  complete the post-resume `GetDescriptor`. The most likely state is the PIE
  still parked in `BUS_EVENT_SW_WAKEUP_3`, i.e. the terminating SE0 did not
  land inside that state. This is a **host-side** problem, not a device bug.
  First confirm the host actually drove something by checking
  `env.host_agent.link_mon.link_svc_trace` for a second row; if it is still
  empty the host half did nothing at all (see "Why not `clear_l1suspend`").
  If it did drive, compare the logged takeover latency against the ~90 us
  budget and consider raising `HOST_L1_RESUME_K_PS`. Do not fix it by
  pre-scheduling the resume.
- `the host takeover did not complete` — the link-service sequence was started
  and never returned. Suspect a busy link-service sequencer or a VIP
  link-state precondition. Host-side again; the device half already passed.

Then narrow a device-half failure down with the firmware-side messages:


- `MCU: L1 wakeup skipped, host did not grant bRemoteWake` — `dev0_lpm_rw`
  never arrived. That is an `LPM_REWP` / token problem, not a wakeup-path
  problem; check `LPM_BREMOTEWAKE` in the sequence and
  `hub_port_lpm_rw_enable(0)` in the waveform.
- `MCU: L1 wakeup skipped, controller not in L1` — the doorbell was rung
  before `LPM_SUS` was set; the L1 entry itself did not happen.
- `MCU: ERROR L1 entered but never exited (LPM_SUS stuck)` — the doorbell was
  accepted but the resume never reached the bus. If the UVM side reports
  `FAILED to complete` then the device half was fine and the host half is at
  fault; if it reports `FAILED at the device half` then check
  `hub_port_enable(0)` and `sync_lpm_rw` at the OR-tree, since both gate
  `hub_lpmremotewakeup`.
- No exit and **none** of the three verdict lines at all — two distinct causes,
  and they look identical in the log:
  1. the run was **truncated** before the verdict ran (see "the verdict can be
     truncated away" above). Compare the last log timestamp against the
     `L1_EXIT_WAIT_MAX` deadline to tell.
  2. `+usb_device_wakeup_check` is missing, so `usb_dut_wakeup_k_seen` never
     fires, no SE0 is driven, and the DUT really does wait forever in
     `BUS_EVENT_SW_WAKEUP_3`, which has no timeout arm. This was the original
     failure mode of this suite.


## Scope

- **DEV0 only.** DEV1 has no software-visible LPM control (`usbreg_lpm_sup`,
  `usbreg_lpmremotewakeup`, `usbreg_lpm_hird_sw`, `usbreg_lpm_nyet` are all
  tied `=> open` at `usb_reg_if_2`), so there is no DEV1 variant.
- **Direct-token path.** The hub-class route into L1,
  `SetAndTestPortFeature(PORT_L1)`, is covered by
  `caliptra_ss_usb_dual_device_hs_hub_port_l1`. Those are the only two L1 entry
  mechanisms; `SetAndTestPortFeature` is legal only against a downstream port,
  never the hub itself, so there is no third "hub-targeted L1" test.

<!-- File contains AI-generated response based on internal company sources -->
