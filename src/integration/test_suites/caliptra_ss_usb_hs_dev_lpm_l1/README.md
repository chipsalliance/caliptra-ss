# High-Speed LPM L1 (Sleep) Entry / Exit Test

**Testcase:** `caliptra_ss_usb_hs_dev_lpm_l1`

## Overview

Brings the upstream USB 2.0 link up at High Speed, enumerates the composite hub
and USBDC0, then makes the host send an **LPM transaction** (EXT token + LPM
token with `bLinkState = 1`) addressed to USBDC0. USBDC0 is expected to ACK it
and enter L1 (Sleep). The link is then brought back to L0, either by the host
(`clear_l1suspend`) or by the device (`DEVCMDSTAT` LPM remote-wakeup write),
selected by a plusarg.

In parallel the MCU firmware polls `DEVCMDSTAT` on USBDC0 and logs and
classifies every `DSUS_C` event as an L1 entry, an L1 exit, or an L2 event.

## Why This Is Not Just Another Suspend Test

L2 suspend is entered by the *absence* of bus activity: the L2 tests simply turn
SOF generation off and wait for the device inactivity timer to expire. **L1 is
not like that.** L1 entry is an explicit packet on the wire. Consequently:

- SOF generation is deliberately left **ON** for the whole of this test. The
  `sof_off` trick used by `caliptra_ss_usb_hs_dev_global_suspend_L2` must not be
  used here; it would produce an L2 suspend and hide the L1 behaviour.
- The stimulus is a Synopsys VIP **protocol service** sequence
  (`svt_usb_protocol_service_usb_20_lpm_sequence`), not a link service one. Only
  the L1 *exit* helpers live under `link_service`.

## Topology (hub-composite IP)

The DUT is the hub-composite USB IP (`ip_xxx_3511_hs_mem_compound_wrapper`): an
on-chip 2-port USB hub with embedded downstream device controllers. USBDC0, the
device the MCU owns in this test, sits *behind* the hub, and its registers are
at `USB_DEV0_REG_BASE_ADDR` (`0x2000_1000`).

As in the other device tests, bring-up is two-phase: `boot_usb_core()` programs
USBDC0 and the hub descriptor RAM, and `main()` must then call
`usb_hub_connect()` so the host sees a connect and drives reset + HS chirp.

The hub's LPM signals *are* wired up through the compound structure
(`ip_xxx_3511_hs_mem_compound_structure.a.vhdl`, `LPM_TM_suspend` / `LPM_RW`
through `usb_synchronizer`). This is the wiring that `hub_port_suspend` was
missing, and is why that test could never pass while this one can. See
`docs/usb_l1_lpm_test_feasibility_report.md` for the full RTL audit.

## Operation

Host-side sequence (`caliptra_ss_usb_hs_dev_lpm_l1_sequence.svh`):

1. Wait for the upstream link to reach `ENABLED`.
2. Start SOF generation and keep it running.
3. Settle (`LINK_SETTLE_DELAY`).
4. Enumerate the hub and USBDC0 (`enumerate_hub_and_usbdc0`). This leaves
   USBDC0 at device address 2, which is why `LPM_DEV_ADDRESS = 7'd2`.
5. Trigger `usb_suspend_stimulus_armed` so the DUT-side checker starts scoring
   only from here (out of reset the DUT holds `SuspendM` low, so a checker
   watching from time zero would score the boot-time transition as a pass).
6. Send the LPM transaction: `bLinkState = 1`, `HIRD = 1`, `bRemoteWake = 1`.
7. Wait for the DUT to enter L1 (`usb_dut_suspend_seen`), bounded by
   `L1_DWELL_MAX`.
8. Exit L1. With `+usb_lpm_dev_wakeup=0` (default) the host drives
   `svt_usb_link_service_clear_l1suspend_sequence`. With `+usb_lpm_dev_wakeup=1`
   the host stays quiet and the firmware drives the exit instead.
9. Poll until the VIP link state is `ENABLED` again, then wait for
   `usb_dut_resume_seen`, bounded by `L1_EXIT_WAIT_MAX`.
10. Short observation window (`POST_EXIT_OBS`), then trigger
    `usb_suspend_resume_obs_window_done` so the checker evaluates its checks.
    This trigger is mandatory; without it no check is evaluated at all.

MCU firmware (`caliptra_ss_usb_hs_dev_lpm_l1.c`):

1. Boots the MCU and USB core, connects the hub, completes the Caliptra
   handshake, and calls `usb_allow_clock_stop()`.
2. Checks `DEVCMDSTAT.LPM_SUP` and logs the reset value of `USB_DEV_LPM`.
3. Polls in a loop servicing bus reset, EP0 SETUP / IN / OUT.
4. On `DSUS_C`, classifies the event from the **live** bits, because `DSUS_C` is
   shared between L1 and L2 in this IP:
   - `LPM_SUS` set -> L1 entry. Records `LPM.HIRD_HW` and `DEVCMDSTAT.LPM_REWP`
     as seen at entry.
   - else `DSUS` set -> an L2 event, logged as *not* L1.
   - else, if an entry was already seen -> L1 exit.
5. Exits the loop once both entry and exit have been seen (not when the poll
   ceiling expires), then halts the MCU with `csr_write_mpmc_halt()`, which is
   what releases the run_phase objection.

## Device-Initiated Exit

Compile the firmware with `USB_LPM_DEVICE_INITIATED_EXIT = 1` and run with
`+usb_lpm_dev_wakeup=1` to exercise the device-driven L1 exit. The firmware then
calls `usb_request_lpm_remote_wakeup()` (in `libs/usb/usb.c`), which is gated on
both `DEVCMDSTAT.LPM_SUS` and `DEVCMDSTAT.LPM_REWP` and performs the wakeup by
writing bit 19 low. Like every `DEVCMDSTAT` read-modify-write in this codebase,
it goes through `usb_devcmdstat_write()`, because bits [6:0] read live but write
a staged copy.

Default is host-initiated exit (`0`), which is the simpler leg to bring up
first.

## What Is Actually Checked

Host side, in the sequence:

- The VIP link returns to `ENABLED` after the L1 exit, within the poll ceiling.
- `usb_dut_suspend_seen` / `usb_dut_resume_seen` must arrive within their
  ceilings.

DUT side, in `caliptra_ss_usb_suspend_resume_checker.sv` (enabled by
`+usb_suspend_resume_check=1`, which the yml passes), watching the active-low
UTMI `SuspendM`:

- `CHK_SUSPEND_SEEN` - the DUT must drive `SuspendM` low, i.e. it really did
  enter the low-power state.
- `CHK_RESUME_SEEN` - having done so, it must drive `SuspendM` high again after
  the exit stimulus.

Firmware-side `DSUS_C` prints are diagnostic only; nothing scores them.

## Scope and Limitations

Read these before trusting a pass.

- **DEV0 only.** At the `usb_reg_if_2` instantiation the four LPM control ports
  (`usbreg_lpm_sup`, `usbreg_lpmremotewakeup`, `usbreg_lpm_hird_sw`,
  `usbreg_lpm_nyet`) are tied `=> open`, so USBDC1 has no software-visible LPM
  control. A dev1 replica of this test would be meaningless and is not
  provided.
- **LPM is not advertised to the host.** There is no BOS / USB 2.0 Extension
  descriptor in this design, and `usb_ep0_hub_descr.m.vhdl` hardcodes
  `bcdUSB = 0x0200`. A real host would therefore never attempt an LPM
  transaction. This test has the VIP send the LPM token unconditionally, which
  is legitimate as an IP-level check of the device's LPM handling but is *not* a
  system-level check that a host would use L1 here.
- **No hub-level L1.** There is no `SetPortFeature(PORT_L1)` support, so
  selective (per-port) L1 is out of scope. What is exercised is the device
  controller's response to an LPM transaction addressed to it.
- **HIRD, not BESL.** This IP implements the HIRD flavour of LPM. The decode is
  in `usb_host_pie.m.vhdl` (HIRD 0 -> 50 us, +75 us per step, 15 -> 1175 us).
  `HIRD = 1` is used here to keep the L1 residency short.
- **`DSUS_C` is shared with L2.** The firmware must classify events from the
  live `LPM_SUS` / `DSUS` bits; a test that assumed `DSUS_C` meant L2 would
  misreport.

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev_lpm_l1_sequence.svh` | Host-side LPM entry / exit sequence |
| `caliptra_ss_usb_hs_dev_lpm_l1_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_dev_lpm_l1.c` | MCU firmware: hub connect, EP0 service, L1 event classification |
| `caliptra_ss_usb_hs_dev_lpm_l1.yml` | Simulation run config, including `+usb_suspend_resume_check=1` |
| `../libs/usb/usb.c` | `usb_request_lpm_remote_wakeup()` helper |
| `../../testbench/caliptra_ss_usb_suspend_resume_checker.sv` | DUT-side checker on UTMI `SuspendM` |
| `../../../../docs/usb_l1_lpm_test_feasibility_report.md` | RTL audit that justified writing this test |

## Running

```
./run_caliptra_test.py -test caliptra_ss_usb_hs_dev_lpm_l1 -sim_dir <dir>
```

Device-initiated exit variant (requires rebuilding the firmware with
`USB_LPM_DEVICE_INITIATED_EXIT = 1`):

```
./run_caliptra_test.py -test caliptra_ss_usb_hs_dev_lpm_l1 -sim_dir <dir> \
    -plusargs +usb_lpm_dev_wakeup=1
```
