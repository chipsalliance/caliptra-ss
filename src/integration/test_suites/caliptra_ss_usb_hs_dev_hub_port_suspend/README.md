# caliptra_ss_usb_hs_dev_hub_port_suspend

USB 2.0 hub **downstream port suspend** test for the on-chip hub-composite USB IP.

> ## Read this first: what a PASS here does and does not mean
>
> Up to USB Hub Release 2.5 of `third_party/usb2`, hub downstream port suspend was
> a **status-only feature** on this IP: the class request was decoded and
> correctly reported, but nothing downstream was ever suspended. Release 2.6
> (submodule commit `97aa961`, pointed to by caliptra-ss `e6090e8c`) wired it
> through, so the request now does suspend the embedded device behind the port.
>
> This test is written to the requirement that was agreed with the designer:
> *"we just care that when the host sends a resume, after that the device is able
> of receiving packets."* That requirement is unchanged by 2.6.
>
> A PASS means the status bit ladder is correct **and** the downstream device
> still answers traffic after the port is resumed. The actuation itself is not
> checked here (see the section below on the suspend/resume checker), so a PASS is
> still not the evidence for it.

## What is being tested

Against hub downstream port 1 (USBDC0), with SOF running throughout:

| Step | Stimulus | Check |
|---|---|---|
| 1 | `GetPortStatus` (baseline) | bit 2 = 0, bit 18 = 0 |
| 2 | `SetPortFeature(PORT_SUSPEND)` | bit 2 = 1, bit 18 = 0 |
| 3 | dwell 600 us, SOF still running | none - just exceeds `T_SUSPEND_DET` |
| 4 | `ClearPortFeature(PORT_SUSPEND)` | bit 2 = 0, bit 18 = 1 |
| 5 | `ClearPortFeature(C_PORT_SUSPEND)` | bit 18 = 0 (write-1-clear works) |
| 6 | `GetDescriptor(Device)` to address 2 | 18 bytes returned, `bDescriptorType` = 1 |

`bit 18 = 0` after the Set in step 2 is not a typo. Both the spec and this RTL
set `C_PORT_SUSPEND` when the **resume** completes, not when the suspend starts.
Expecting `1` there would file a phantom bug against RTL that is correct.

The 600 us dwell is three times the simulation `T_SUSPEND_DET` of 200 us
(`G_SIM_CHIRP_TIMERS=1`), so a hub that did gate downstream traffic would have
had ample time to make the device suspend. With 2.6 that is what happens, and the
dwell gives the suspended state a realistic duration before the resume.

### Step 6 is the load-bearing check

Steps 1-5 are register readbacks. On their own they would be a status test that
passes without observing any device behaviour - the failure mode this project has
been burned by before (see the FS suspend/resume test fixed in `b3ac08c`).

Step 6 makes the test mean something: it re-anchors the host VIP to device
address 2 and issues a real control transfer to the downstream device *after*
the resume, and inspects the returned payload. It is the direct executable form
of the stated requirement.

A **control** transfer is used, not bulk. The firmware here is a passive EP0
observer that never arms EP1 buffers, so a bulk OUT would be NAKed forever and
fail for a reason unrelated to the feature under test.
`GetDescriptor(Device)` is already known serviceable - `usbdc0_enum_stepC` issues
the same request during enumeration.

## What this test deliberately does not do

It does **not** enable `caliptra_ss_usb_suspend_resume_checker`
(`+usb_suspend_resume_check`). That checker owns `CHK_SUSPEND_SEEN`, which
watches UTMI `SuspendM`, and it is a hard pass/fail for
`caliptra_ss_usb_hs_dev_global_suspend_L2` and `caliptra_ss_usb_fs_dev_global_suspend_L2`
where global suspend actuates the upstream link.

This test was kept out of the checker when per-port suspend was status-only,
because enabling it would have failed forever. With 2.6 the port request does
reach the device controller, but it does not necessarily reach UTMI `SuspendM`
in the same way a global suspend does, so the checker is still not enabled here
and the actuation is not claimed as a check. Revisiting this is a possible
follow-up now that the path exists.

## How the port request reaches the device - 2.6 and later

In `third_party/usb2/src/usb_hub_composite_device/RTL/RTL/usb_app_hw_hub.m.vhdl`
the signal that tracks the per-port request was renamed to
`hub_port_suspend_int`, and `hub_port_suspend` became an entity **output**
(alongside the new `hub_port_l1`), driven by `hub_port_suspend <=
hub_port_suspend_int;`. Before 2.6 it was a module-local signal with no output
assignment, used only to drive `hub_status(i+1)(2)`.

In `ip_xxx_3511_hs_mem_compound_structure.a.vhdl` the device controllers used to
receive the raw upstream suspend (`sync_suspend => sync_suspend`). 2.6 inserts a
per-device term:

```
dev0_suspend <= (sync_suspend and hub_port_enable(0)) or hub_port_suspend(0)
                  when hub_enable_q = '1' else sync_suspend;
dev1_suspend <= (sync_suspend and hub_port_enable(1)) or hub_port_suspend(1);
```

with the equivalent for `*_lpm_suspend` via `hub_port_l1`. So
`SetPortFeature(PORT_SUSPEND)` now suspends the embedded device on that port and
`DEVCMDSTAT.DSUS_C` sets; `ClearPortFeature(PORT_SUSPEND)` produces the second
`DSUS_C`.

Historical note: the previous version of this section explained why the actuation
did **not** exist (internal-only `hub_port_suspend`, no per-port traffic gate,
globally inferred suspend shared between both device instances). That is accurate
for 2.5 and earlier only.

## Firmware role

`caliptra_ss_usb_hs_dev_hub_port_suspend.c` is a passive device-side observer. It
boots USBDC0 behind the hub, connects the hub upstream, serves EP0 so the host
can enumerate, and logs `DEVCMDSTAT.DSUS_C` transitions.

There is **no firmware register write that can suspend a downstream port**, and
none is attempted: the hub's EP0 SETUP-match decode is an RTL ROM and
`SetHubPortFeature` is already present in it, so the request is accepted (not
STALLed) with no firmware involvement.

The `DSUS_C` count is printed but is never a pass or fail. With 2.6 and later the
expected count is `2`, one for entering suspend and one for leaving; on 2.5 and
earlier it was `0`. Either way it is logged only as a cross-check of the
device-side view next to the host-side status ladder, and it must not influence
when the firmware stops serving EP0 - ending the poll loop on this count used to
make the post-resume check fail.

### When the firmware halts

The firmware must outlive the host-side ladder, because the final host check is a
control transfer *to this device*: halting early would make that check fail for a
firmware reason rather than a design one. But it must not outlive it by much,
since nothing can end the run while the MCU is alive - `caliptra_ss_usb_base_test`
holds a `run_phase` objection in `mcu_halt_monitor_task()` until the firmware
reaches `csr_write_mpmc_halt()`.

So the firmware halts on a **host-observable event**, not on a timer: it counts
`GetDescriptor(Device)` requests served *after* `SET_ADDRESS`, and once the second
one has been answered - that is `post_resume_traffic_check()`, the last thing the
host asks of this device - it serves a short grace window and halts.

```
MCU: post-resume GetDescriptor(Device) served (device-descriptor read 2 at the assigned address) ...
MCU: grace window of 500 polls served after the post-resume check; ending poll loop at poll ...
MCU: hs_dev_hub_port_suspend test complete
```

`USB_POLL_TIMEOUT` remains only as a **safety fallback** so a build where that
request never arrives still terminates instead of hanging the regression. Taking
it is abnormal and says so explicitly:

```
MCU: WARNING poll ceiling of 50000 reached without serving the post-resume GetDescriptor(Device) ...
```

If that warning appears, the host-side post-resume check cannot have passed
either, so look for the UVM sequence error in the same log rather than treating
it as a firmware problem. Note that if the sequence is ever extended to read the
device descriptor again *after* the post-resume check, `USB_POSTRESUME_DESC_COUNT`
must be raised to match, or the firmware will halt before that later transfer.


## Running

```sh
source caliptra_setup_env.csh          # or tools/caliptra_env_setup.sh
tools/run_caliptra_test.py -test caliptra_ss_usb_hs_dev_hub_port_suspend \
                           -sim_dir /scratch/$USER/hub_port_suspend
```

The top-level `run_caliptra_test_*.log` only echoes the `bsub` command. **The
real verdict is in `<sim_dir>/vcs_sim.log`.**

What to look for there:

```
USB_HS_HUB_PSUSP_SEQ ... baseline:  port 1 status bit 2  (PORT_SUSPEND)   = 0 as expected
USB_HS_HUB_PSUSP_SEQ ... postSet:   port 1 status bit 2  (PORT_SUSPEND)   = 1 as expected
USB_HS_HUB_PSUSP_SEQ ... postSet:   port 1 status bit 18 (C_PORT_SUSPEND) = 0 as expected
USB_HS_HUB_PSUSP_SEQ ... postClear: port 1 status bit 2  (PORT_SUSPEND)   = 0 as expected
USB_HS_HUB_PSUSP_SEQ ... postClear: port 1 status bit 18 (C_PORT_SUSPEND) = 1 as expected
USB_HS_HUB_PSUSP_SEQ ... postAck:   port 1 status bit 18 (C_PORT_SUSPEND) = 0 as expected
USB_HS_HUB_PSUSP_SEQ ... postResume: device descriptor returned ... device answers traffic after resume
```

Interpreting failures:

- a **status-plane** check failing means the class request is no longer decoded
  or routed to the right port;
- **step 6 failing** is the important one: the downstream device stopped
  answering after `ClearPortFeature(PORT_SUSPEND)`. That breaks the one
  requirement this IP does claim to meet and must be investigated, not waived;
- both failing together usually means the run broke before the feature under
  test (enumeration, hub connect, clock), so it says nothing about port suspend.

## Scope

- **HS, dev0 only.** This test exercises the *hub*, not a device controller, so
  the usual dev0/dev1 and HS/FS families do not apply and
  `tools/scripts/gen_usb_dev_variants.py` needs no change.
- The hub IP is a submodule and is **not patched** here.

## Files

| File | Role |
|---|---|
| `caliptra_ss_usb_hs_dev_hub_port_suspend.c` | MCU firmware, passive EP0 observer |
| `caliptra_ss_usb_hs_dev_hub_port_suspend.yml` | test config, `+UVM_TESTNAME` only |
| `caliptra_isr.h`, `cptra_bringup.c` | unmodified copies of the standard USB-test support files |
| `../../testbench/uvm/usb/caliptra_ss_usb_hs_dev_hub_port_suspend_sequence.svh` | host stimulus, status ladder and post-resume traffic check |
| `../../testbench/uvm/usb/caliptra_ss_usb_hs_dev_hub_port_suspend_test.svh` | UVM test wrapper |

<!-- File contains AI-generated response based on internal company sources -->
