# High-Speed LPM L1 (Sleep) Entry / Exit Test

**Testcase:** `caliptra_ss_usb_hs_dev_lpm_l1`

## Overview

Brings the upstream USB 2.0 link up at High Speed, enumerates the composite hub
and USBDC0, then makes the host send an **LPM transaction** (EXT token + LPM
token with `bLinkState = 1`) addressed directly to USBDC0. USBDC0 is expected to
ACK it and enter L1 (Sleep). The link is then brought back to L0, either by the
host (`clear_l1suspend`) or by the device (`DEVCMDSTAT` LPM remote-wakeup
write), selected by a plusarg.

In parallel the MCU firmware polls `DEVCMDSTAT` on USBDC0 and logs and
classifies every `DSUS_C` event as an L1 entry, an L1 exit, or an L2 event.

## Scope of This Test vs the Hub-Level L1 Test

This is the **device-controller / PIE-level** LPM check: the LPM token is
addressed to the device controller behind the hub, which is the IP-level entry
path into L1.

Since release_2.6 the hub front-end also implements
`SetAndTestPortFeature(PORT_L1)`, so a real host can now put a downstream port
into L1 through the hub. That path is covered by a separate test and is
deliberately **not** folded into this one, because it exercises a different
mechanism (a hub class control transfer dispatched by `usb_app_hw_hub`, not a
raw LPM token decoded by the PIE).

There are exactly **two** ways into L1 in this IP, and both of them ultimately
name a *device*:

| Test | Mechanism | Target |
|------|-----------|--------|
| `caliptra_ss_usb_hs_dev_lpm_l1` (this test) | EXT + LPM token, decoded by the PIE | USBDC0's bus address |
| `caliptra_ss_usb_dual_device_hs_hub_port_l1` | `SetAndTestPortFeature(PORT_L1)` control transfer to the hub, with the SUCCESS / NYET / STALL-code response ladder | downstream port 1 (DEV0) and port 2 (DEV1), independently |

There is deliberately **no** third "hub-targeted L1" test, because no such
request exists: `SetAndTestPortFeature(PORT_L1)` is only legal against a
downstream port. A `wIndex[3:0]` port field of `0` - i.e. the hub itself - is
rejected with a protocol STALL by `usb_app_hw_hub.m.vhdl`:

```vhdl
when C_CLASS_REQ_SET_AND_TEST =>
  if to_integer(unsigned(ep0_windex(3 downto 0))) = 0 then
    null; -- A stall will be returned upon this request
```

and `hub_port_l1` is a per-port vector (`C_HUB_NB_PORTS-1 downto 0`) with no
broadcast form. "Global" L1 in the sense of one request suspending the whole
hub is not a feature of this design.

Both mechanisms end up asserting the same device-visible state: in the compound
structure `devN_lpm_suspend <= (sync_lpm_suspend and hub_port_enable(N)) or
hub_port_l1(N)`, so hub-driven PORT_L1 reaches `DEVCMDSTAT.LPM_SUS` / `DSUS_C`
exactly as the direct token does. The firmware classification logic in this
test is therefore reusable unchanged by the hub-level test.


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

- **Direct-token path is DEV0 only.** The LPM token in this test is addressed to
  USBDC0. USBDC1 still has no software-visible LPM *control* of its own, so a
  dev1 replica of *this* test is not provided.

  This is no longer a limitation on L1 coverage as a whole. In the compound
  structure `hub_port_lpm_sup(0) <= dev0_lpm_sup` and
  `hub_port_lpm_sup(1) <= dev1_lpm_sup`, with the matching per-port
  `hub_port_lpm_data_pending` / `hub_port_lpm_hird_sw` wiring, and
  `hub_port_l1(N)` feeds `devN_lpm_suspend`. Both ports are therefore reachable
  and independently steerable **through the hub**, which is exactly what
  `caliptra_ss_usb_dual_device_hs_hub_port_l1` covers.
- **LPM *is* advertised to the host.** The hub DEVICE descriptor reports
  `bcdUSB = 0x0210` and the hub exposes a 12-byte BOS containing a USB 2.0
  Extension device capability with the LPM bit set (`bmAttributes = 0x02`).
  This is what makes an LPM transaction legal for a real host, and it is checked
  independently by `caliptra_ss_usb_hs_dev_get_bos_descriptor` and
  `caliptra_ss_usb_fs_dev_get_bos_descriptor` via `check_bos_descriptor()`.

  Residual RTL inconsistency worth knowing about: the hub **DEVICE_QUALIFIER**
  descriptor still reports `bcdUSB = 0x0200` while the DEVICE descriptor reports
  `0x0210`. Harmless for this test, but it is a spec inconsistency in
  `usb_ep0_hub_descr.m.vhdl`, not a testbench bug.
- **Hub-level L1 exists, and is covered elsewhere.** `usb_app_hw_hub.m.vhdl`
  implements `SetAndTestPortFeature(PORT_L1)` (`bmRequestType = 0xA3`,
  `bRequest = 0x0C`, `wValue = 10`, `wLength = 1`) with `wIndex[3:0]` = 1-based
  port, `wIndex[7:4]` = HIRD, `wIndex[15]` = remote-wake enable, and a
  one-byte response of `0x00` SUCCESS / `0x10` NYET / `0x30` STALL-code.
  The request is **downstream-port-only**: a port field of `0`, naming the hub
  itself, is answered with a protocol STALL, and there is no broadcast encoding.
  Selective per-port L1 is therefore **in** scope for the design and is covered
  by `caliptra_ss_usb_dual_device_hs_hub_port_l1`. What *this* test still
  uniquely covers is the device controller's own response to an LPM token
  addressed directly to it, which no hub-class request exercises.
- **HIRD, not BESL.** This IP implements the HIRD flavour of LPM. The decode is
  in `usb_host_pie.m.vhdl` (HIRD 0 -> 50 us, +75 us per step, 15 -> 1175 us).
  `HIRD = 1` is used here to keep the L1 residency short.

  Naming caveat for anyone reading the register model: the hub LPM register is
  described in `systemrdl/usb_hub.rdl` with fields named `BESL_SW` / `BESL_HW`,
  but the RTL it documents (`hub_lpm_hird_sw` / `hub_lpm_hird_hw`) is the HIRD
  encoding. The names differ; the semantics are HIRD.
- **`DSUS_C` is shared with L2.** The firmware must classify events from the
  live `LPM_SUS` / `DSUS` bits; a test that assumed `DSUS_C` meant L2 would
  misreport. This is unchanged by the hub path: hub-driven PORT_L1 arrives on
  the same `devN_lpm_suspend` net, so the same classification is required there.


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
