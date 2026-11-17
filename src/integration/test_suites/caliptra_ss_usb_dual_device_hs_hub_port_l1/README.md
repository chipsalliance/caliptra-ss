# caliptra_ss_usb_dual_device_hs_hub_port_l1

Hub-request USB 2.0 LPM / L1 test. The host issues `SetAndTestPortFeature(PORT_L1)`
to the on-chip hub naming **port 1** and then **port 2**, and checks the request
encoding, the response ladder, and that each request affects *only* its own port
and its own embedded device controller.

## The two L1 scenarios, and why there are only two

This IP has exactly two ways to put a device into L1, and **both target a
device** - never the hub:

| Scenario | Stimulus | Addressed to | Decoded by | Test |
|---|---|---|---|---|
| Direct token | EXT + LPM token (a link-layer packet) | the device's own bus address | `usb_pie.m.vhdl` | `caliptra_ss_usb_hs_dev_lpm_l1` (USBDC0 only) |
| Hub request | `SetAndTestPortFeature(PORT_L1)` control transfer | the hub, naming a **downstream port** in `wIndex[3:0]` | `usb_app_hw_hub.m.vhdl` | **this test**, for both devices |

There is no third "hub-targeted L1" scenario, because the request is illegal
against the hub itself. From `usb_app_hw_hub.m.vhdl`:

```vhdl
when C_CLASS_REQ_SET_AND_TEST =>
  if to_integer(unsigned(ep0_windex(3 downto 0))) = 0 then
    null; -- A stall will be returned upon this request
  elsif to_integer(unsigned(ep0_windex(3 downto 0))) <= C_HUB_NB_PORTS then
```

A `wIndex` port field of `0` is how a hub-class request addresses the hub
itself, and it is rejected. This test asserts that as a negative case rather
than leaving it as a comment.

## Request encoding

`SetAndTestPortFeature(PORT_L1)` does **not** use the usual `SetPortFeature`
layout:

| Field | Value | Notes |
|---|---|---|
| `bmRequestType` | `0xA3` | `DEVICE_TO_HOST` / `CLASS` / `BMREQ_OTHER` - it returns a data byte |
| `bRequest` | `0x0C` | `SetAndTestPortFeature` |
| `wValue` | `10` | `PORT_L1`. Any other selector is ignored |
| `wIndex[3:0]` | 1-based port number | **four** bits, not eight. `0` or `> C_HUB_NB_PORTS` STALLs |
| `wIndex[7:4]` | HIRD | must be `>=` the port's `HIRD_SW` |
| `wIndex[15]` | remote-wake enable | |
| `wLength` | `1` | one status byte is returned |

Response byte, from `hub_l1_status`:

| Value | Meaning |
|---|---|
| `0x00` | SUCCESS - the port entered L1 |
| `0x10` | NYET - `DATA_PENDING` set, or `HIRD_SW > HIRD_HW` |
| `0x30` | STALL-code - `hub_lpm_sup(port)` clear. A **data byte**, not a protocol STALL |

## Why a dual-device image

Two per-port wiring facts in `ip_xxx_3511_hs_mem_compound_structure.a.vhdl`
force this.

1. The hub's **response** comes from the DEVICE CSRs, per port:

   ```
   hub_lpm_sup(0)          <= dev0_lpm_sup       -- DEV0 DEVCMDSTAT[11] LPM_SUP
   hub_lpm_data_pending(0) <= dev0_lpm_nyet      -- DEV0 LPM[8]  DATA_PENDING
   hub_port_lpm_hird_sw(0) <= dev0_lpm_hird_sw   -- DEV0 LPM[7:4] HIRD_SW
   hub_lpm_sup(1)          <= dev1_lpm_sup       -- DEV1, same fields, port 2
   ```

   Port 2 can only answer SUCCESS if USBDC1 is booted with `LPM_SUP` set. A
   single-device image would also leave USBDC1 without EP0 service, so it would
   never enumerate and port 2 could not be brought up at all.

2. The **L1 level** reaches the device per port:

   ```
   devN_lpm_suspend <= (sync_lpm_suspend and hub_port_enable(N)) or hub_port_l1(N)
   ```

   This is what makes the isolation claim observable from firmware, and also why
   a hub-driven L1 is indistinguishable from a direct LPM token on the device
   side - both land on the same net as `DEVCMDSTAT.LPM_SUS` + shared `DSUS_C`.

## Response modes

The firmware decides which answer the host sees, because the hub reads the
per-port device CSRs. Selected at build time and declared to the sequence with
a matching plusarg - **the two must always be changed together**:

| `USB_HUB_L1_RESPONSE_MODE` | How | Expected response | Port enters L1? | Plusarg |
|---|---|---|---|---|
| 0 (default) | `LPM_SUP=1`, `HIRD_SW=0` on both | `0x00` SUCCESS | yes | `+usb_hub_l1_expect=0` |
| 1 | `HIRD_SW=0xF` on both | `0x10` NYET | no | `+usb_hub_l1_expect=1` |
| 2 | `DEVCMDSTAT.LPM_SUP` cleared on both | `0x30` STALL-code | no | `+usb_hub_l1_expect=2` |

NYET is forced via `HIRD_SW` rather than `DATA_PENDING` because the latter also
has a hardware writer and would make the refusal racy.

## Operation

1. Firmware boots USBDC0 and USBDC1, programs the response mode on both, then
   connects the hub upstream and releases `FORCE_NEEDCLK` on both.
2. Host enumerates the hub (addr 1), port 1 + USBDC0 (addr 2), port 2 + USBDC1
   (addr 3).
3. Baseline: both ports `PORT_L1 = 0`, `C_PORT_L1 = 0`.
4. Negative cases - all must STALL, and both ports must still be idle after:
   port field `0` (the hub itself), port field `3` (out of range), and a
   `wValue` that is not `PORT_L1`.
5. Port 1 leg: the request must return the declared response byte; port 1's
   state must match the declared expectation **and port 2 must be untouched**.
6. Clear port 1 (`PORT_L1` then `C_PORT_L1`); both ports idle again.
7. Port 2 leg: mirror of step 5, with port 1 as the isolation check.
8. Clear port 2.
9. Both devices must still answer control traffic.
10. The firmware halts, via a two-stage exit described below.

### How the firmware decides to halt

This matters more than it looks, because the MCU halt is what ends the whole
simulation: `caliptra_ss_usb_base_test` only drops its `run_phase` objection on
the halt. Get it wrong in one direction and the run looks like a hang; wrong in
the other and the host's final checks fail against a device that has already
stopped answering.

- **Stage 1** waits until both controllers have reached their expected L1 entry
  and exit counts with neither still in L1. The latch is taken **once**, so a
  spurious later entry cannot postpone the halt forever - it is still counted
  and still reported by the verdict.
- **Stage 2** then waits for `USB_HUB_L1_TAIL_SETUPS` further EP0 SETUPs on
  **each** controller, which is the host's closing `GetDescriptor` to address 2
  and address 3 from step 9. Only then does the MCU halt.

Stage 2 is counted in **SETUPs, not poll iterations**, and that distinction is
the whole point. Stage 1 completes while the host is still clearing port 2, so
halting there leaves the step 9 transfers unanswered - they come back as
`returned 0 payload bytes` after a NAK timeout, which reads as a device fault
rather than as firmware that stopped early. A poll-iteration grace period
cannot fix this reliably: iterations bear no fixed relation to host progress, so
any constant is either too short or arbitrarily long. Counting SETUPs ties the
halt directly to the host's own traffic.

`USB_HUB_L1_TAIL_POLL_MAX` bounds stage 2 so a host that never sends those
SETUPs cannot hang the run; reaching it prints a warning naming the likely
causes. If step 9 ever grows another transfer per device, raise
`USB_HUB_L1_TAIL_SETUPS` to match.

## Checks

Host side - the load-bearing ones are the isolation checks:

- Both ports idle at baseline, after the negative cases, and after each exit.
- All three negative cases STALL. `results_status[4]` is inspected directly,
  because `check_xfer_status()` treats a STALL as a failure; the **absence** of
  the STALL is the error.
- The response byte matches the declared mode exactly.
- After each request, the *other* port's `PORT_L1` and `C_PORT_L1` are still 0.
- Both device addresses answer a well-formed device descriptor afterwards.

Device side (firmware, corroborating):

- Each controller sees exactly the expected number of L1 entries (1 in the
  SUCCESS build, 0 in a refusal build). A count of **2** in either build means
  the other port's request suspended it too - the isolation failure.
- Entry and exit counts match; neither controller is left in L1.
- No L2 suspends (SOF stays on for the whole test).

## Scope and limitations

- **The DUT-side suspend/resume checker is deliberately NOT armed.**
  `caliptra_ss_usb_suspend_resume_checker` watches the single shared UTMI
  `SuspendM` for the whole compound IP, so it cannot attribute a suspend to one
  port. The "a real low-power link state was entered" claim against that signal
  belongs to `caliptra_ss_usb_hs_dev_lpm_l1`, which does arm it.
- **`C_PORT_L1` is set on ENTRY**, unlike `PORT_SUSPEND` whose change bit sets
  on *resume*. The sequence expects `C_PORT_L1 = 1` immediately after a
  successful entry. Do not "fix" this to 0 - see `GEN_HUB_PORT_STATUS`.
- **The two port legs are sequential, not simultaneous.** Driving both ports
  into L1 at once is a reasonable follow-up scenario but is not what this test
  claims; "the other port is unaffected" only needs one port active at a time.
- **L1 entry is confirmed by polling, not by waiting.** `wait_port_l1_set()`
  re-reads `GetPortStatus` until `PORT_L1` comes back set, bounded by
  `L1_ENTRY_POLL_MAX` reads, and normally succeeds on the first read because
  `hub_port_l1_int` is set in the same clocked branch that handles the request.
  The earlier flat `100 us` dwell per port has been removed: it cost time
  unconditionally and, worse, made every observation late enough to hide a slow
  entry. A timeout in the poll is deliberately *not* an error - the
  `check_port_bit()` call immediately after is what reports the failure, so a
  single defect is not double-reported.
- **The refusal modes apply to both ports at once.** Mixed per-port responses
  (port 1 SUCCESS while port 2 NYET) would be a further scenario; it is not
  covered, and would need the firmware to program the two controllers
  differently.
- **HIRD, not BESL.** This IP decodes HIRD (`usb_host_pie.m.vhdl`: 50us + 75us
  per step). The RDL names `BESL_SW` / `BESL_HW` are misleading.
- **`DSUS_C` is shared between L1 and L2**, so the firmware classifies from the
  live state bits rather than assuming which one moved.

## Running

```bash
# SUCCESS leg (the default, and what the .yml runs).
make -C $CALIPTRA_SS_ROOT/tools/scripts \
     TESTNAME=caliptra_ss_usb_dual_device_hs_hub_port_l1 \
     CALIPTRA_TESTNAME=cptra_bringup CALIPTRA_AUX=soc_ifc_ss \
     CALIPTRA_SS_CLK_FREQ=400 \
     mcu_program.hex cptra_program.hex

# NYET leg - also change the plusarg to +usb_hub_l1_expect=1.
make ... BUILD_CFLAGS="-DUSB_HUB_L1_RESPONSE_MODE=1" ...

# STALL-code leg - also change the plusarg to +usb_hub_l1_expect=2.
make ... BUILD_CFLAGS="-DUSB_HUB_L1_RESPONSE_MODE=2" ...
```

This image must **not** be built with `-DUSB_DEV_SEL=1`: that would
compile-time pin the shared USB library to a single controller and leave port 2
with no device behind it.

<!-- File contains AI-generated response based on internal company sources -->
