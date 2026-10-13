# Structured debug: `caliptra_ss_usb_dual_device_hs_dev0_hotplug`

Evidence base: `regressions/caliptra_ss_usb_dual_device_hs_dev0_hotplug/`
(`vcs_sim.log`, `mcu_console.log`, `env.host_agent.prot_mon.HS.xfer_trace`,
`env.host_agent.link_mon.20.RX.pkt_trace`). Run of Oct 13 15:00, sim end
801166 ns, 3 UVM_ERRORs.

---

## 0. Headline: you are chasing the wrong error

The three `valid_device_response_check_Dev3_EP0` UVM_ERRORs are a **symptom**,
and they are not even the test's real failure. The real failure is:

> **USBDC1 never gets configured. All four of its post-SET_ADDRESS control
> transfers were ABORTED by the VIP, and the sequence reported
> "Dual-device enumeration complete" anyway.**

Because USBDC1 is never configured, `dev1_loops` stays 0, `HP_WAIT_DEV1_UP`
never releases, and `dev0_cycles` stays **0/3** - i.e. the DEV0 hotplug cycling
that is the entire purpose of this test **never executes at all**. The run ends
on the `mcu_halt_timeout`, not on a verdict.

This is why nine rounds of logic fixes (rounds 8/9, EP0 `NBytes`, EP1 `Active`,
toggle reset, ...) have not moved the needle: **none of them is the active bug
any more.** The firmware is no longer deadlocked. It is simply *too slow*, and
the sequence is *too permissive* to say so.

---

## 1. What the logs prove

### 1.1 Every DEV1 addr-3 transfer ABORTED with zero payload

From `prot_mon.HS.xfer_trace` - the VIP's own transfer-level verdict column:

| Start (ns) | End (ns) | Transfer | D_adr | Pld | Status |
|---|---|---|---|---|---|
| 685647 | 691830 | `CONTROL_TRANSFER(GET_DESCRIPTOR)` | 3 | **0** | **ABORTED** |
| 691880 | 692780 | `CONTROL_TRANSFER(GET_CONFIGURATION)` | 3 | **0** | **ABORTED** |
| 692847 | 693930 | `CONTROL_TRANSFER(SET_CONFIGURATION)` | 3 | **0** | **ABORTED** |
| 694330 | 695230 | `CONTROL_TRANSFER(GET_CONFIGURATION)` | 3 | **0** | **ABORTED** |

Contrast DEV0 (addr 2), same code path, same sequence task:

| Start (ns) | End (ns) | Transfer | D_adr | Pld | Status |
|---|---|---|---|---|---|
| 538903 | 542686 | `CONTROL_TRANSFER(GET_DESCRIPTOR)` | 2 | 18 | ACCEPT |
| 543069 | 547802 | `CONTROL_TRANSFER(GET_CONFIGURATION)` | 2 | 1 | ACCEPT |

DEV0: 100% ACCEPT with real payloads. DEV1: 100% ABORTED with no payload.
**This is a binary, unambiguous discriminator and it is already in the logs.**

### 1.2 The MCU went dark for 14 us in exactly that window

`mcu_console` SETUP servicing for DEV1:

```
673377  SETUP handled bReq=0x6   GET_DESCRIPTOR (addr 0)
678707  SETUP handled bReq=0x0   GET_STATUS
683352  SETUP handled bReq=0x5   SET_ADDRESS -> 3
684357  SET_ADDRESS addr=3
        ---- 14.0 us with ZERO SETUP servicing ----
698352  SETUP handled bReq=0x6   GET_DESCRIPTOR  (12.7 us LATE, host already aborted it)
```

`bReq=0x8` (GET_CONFIGURATION) and `bReq=0x9` (SET_CONFIGURATION) are **never
serviced for DEV1**. DEV0 got its `bReq=0x9` at 555647 and enumerated 1.4 us
later.

The four host transfers in 1.1 all live inside that 14 us dead zone.

### 1.3 The hardware was healthy - this is pure firmware latency

The progress dump at **693082 ns**, taken in the middle of the dead zone, is
decisive:

```
dev1 ... addr=3 DEVCMDSTAT=0x10814B83 ep0out=0x80004005 ep1out=0x0 ep1in=0x0
```

| Field | Value | Meaning |
|---|---|---|
| `DEVCMDSTAT` bit 8 (`SETUP`, 0x100) | **1** (`0x...B83`) | a SETUP **is pending and unserviced** |
| `DEVCMDSTAT[6:0]` (`DEV_ADDR`) | **3** | address was applied correctly and in time |
| `ep0out` | `0x80004005` | `Active`=1, `NBytes`=8 - **correctly armed**, no decay |
| `ep1out` / `ep1in` | `0x0` | EP1 never armed -> device never configured |

So: the controller **received the SETUP fine**, EP0 OUT was **properly armed
with NBytes=8** (the round-10 `NBytes` decay bug is genuinely fixed), the
address was **correct**. The only thing missing is firmware *decoding it in
time*. The device therefore NAKs while the host retries, and the VIP correctly
flags the NAK-to-SETUP protocol violation before giving up and aborting.

This rules out, with log evidence, every hypothesis the README is built around:

| Previously suspected | Status | Disproving evidence |
|---|---|---|
| EP0 OUT `NBytes` decay | **RULED OUT** | `ep0out=0x80004005` (NBytes=8) at the failure |
| EP0 lost-interrupt deadlock (round 8) | **RULED OUT** | SETUP *was* serviced at 698352 - EP0 recovered |
| `usb_ep0_out_unarmed()` gating deadlock (round 9) | **RULED OUT** | `DEVCMDSTAT.SETUP` gate is in place and fires |
| EP1 `Active` two-phase livelock | **NOT REACHED** | EP1 never armed; device never configured |
| DEV1 isolation violation (bus reset / addr loss) | **NOT REACHED** | `addr=3` held, no `DRES_C`, `dev0_cycles=0` |
| `POST_PORT_RESET_SETTLE` too short | **RULED OUT** | 80 us was applied; failure is 100+ us later |

### 1.4 The blocking agent is the progress dump itself

The dump is **two `VPRINTF`s totalling ~184 characters**, each character a store
to `SOC_MCI_TOP_MCI_REG_DEBUG_OUT`, emitted from inside the poll loop. Measured
cost from the log (`693082` dump line -> `698352` next line): **~5.3 us**, i.e.
~28.6 ns/char at 400 MHz.

The host spaces enumeration SETUPs **~5 us apart**. A 5.3 us blackout is
therefore *guaranteed* to drop at least one SETUP, and USB 2.0 s8.5.3 forbids
NAKing a SETUP.

The dump cadence is `USB_PROGRESS_DUMP_US = 100`. DEV1's enumeration window is
~30 us wide (666851 -> 695232). The dump at 693082 lands inside it. DEV0's
window was ~40 us and no dump landed in it - **DEV0 passed purely by luck of
phase.** Because the cadence is `mcycle`-anchored and the sim is deterministic,
it lands in the same place every run, which is exactly why you see "still the
same error".

> **The diagnostic added to find the bug has become the bug.** This is the
> classic heisenbug inversion, and it is the single highest-value finding here.

### 1.5 Second, independent bug: the test cannot fail

At 691832 ns, immediately after a transfer the VIP marked **ABORTED with 0
payload bytes**, the sequence logged:

```
[USB_DATA_CHECK_API_IMPL] dev1 device address checked (expected=3 got=3)
[USB_DEV0_HOTPLUG_SEQ]    Dual-device enumeration complete (USBDC0@2, USBDC1@3)
```

The address check **passed on an empty, aborted payload** - it is reading a
stale or default buffer. The sequence then declared enumeration complete and
proceeded into `dev1_loopback("baseline")` against an unconfigured device.

Neither `usbdc0_enum_stepC()` nor `wait_xfer_done()` inspects
`svt_usb_transfer::status`. Four ABORTED transfers produced **zero sequence-level
errors**. The README's own principle - *"A test that cannot fail is worse than
no test at all"* - applies again, one level up: it was fixed in the firmware's
isolation check but the same defect is still live in the host sequence.

**This is what has been costing you the debug effort**: the log says
"enumeration complete", so attention goes to the downstream NAK errors instead
of to the enumeration that visibly did not happen.

---

## 2. Root cause

```
USB_PROGRESS_DUMP_US = 100 us cadence, ~184-char VPRINTF inside the poll loop
        |
        v
~5.3 us window in which the MCU services no EP0 SETUP
        |
        v
lands inside USBDC1's ~30 us enumeration window (deterministic phase)
        |
        v
device NAKs SETUPs  ->  3x valid_device_response_check_Dev3_EP0   [the visible error]
        |
        v
VIP aborts 4 control transfers, incl. SET_CONFIGURATION
        |
        v
usb_is_configured()==false for dev1 forever -> EP1 never armed -> dev1_loops=0
        |
        v
HP_WAIT_DEV1_UP never releases -> dev0_cycles=0/3
        |
        v
THE TEST'S ENTIRE PURPOSE NEVER RUNS, and the sequence reports
"Dual-device enumeration complete" because it ignores transfer status
```

Primary cause: **EP0 SETUP service latency inflated above the host's control
transfer timeout by in-loop `VPRINTF` diagnostics.**
Masking cause: **host sequence does not check `svt_usb_transfer::status`.**

---

## 3. Fix plan, in dependency order

### Track A - stop the test from lying (do this FIRST)

Without this you cannot trust any subsequent experiment. It is also pure test
code, zero risk to the DUT/firmware.

1. In `caliptra_ss_usb_base_sequence.svh::wait_xfer_done()` (or a new
   `check_xfer_status()`), raise a `uvm_error` when a completed transfer's
   `status` is not `ACCEPT`/complete, naming the label.
2. In `usbdc0_enum_stepC()`, require a non-zero payload on
   `GET_DESC_DEV_addr2` and `GET_CONFIG_verify` before declaring success.
3. Make `caliptra_ss_usb_data_check_api_impl.svh` address/config checks fail
   (not pass) when `payload_byte_count()==0`.

Expected result on a re-run with no other change: the run fails at
**~685 us on an ABORTED GET_DESCRIPTOR for Dev3**, instead of limping to a
timeout 115 us later. The error then points at the real defect.

### Track B - remove the latency (the actual fix)

Options, best first:

| # | Change | Risk | Note |
|---|---|---|---|
| B1 | Gate the progress dump on `dev0_cycle_count > 0` (i.e. only dump once the hotplug phase has started, never during enumeration) | very low | keeps full diagnostics where they matter, removes them from the critical window |
| B2 | Raise `USB_PROGRESS_DUMP_US` 100 -> 1000 | very low | reduces hit probability ~10x but does **not** eliminate it; phase is deterministic so it may simply move the collision |
| B3 | Shrink the dump to one short line (<40 chars) | low | ~1.1 us blackout; still marginal against 5 us SETUP spacing |
| B4 | Suppress the dump whenever `DEVCMDSTAT.SETUP` is set on either controller, deferring it one iteration | low | directly expresses the invariant: never print while a SETUP is pending |
| B5 | Service EP0 for both controllers once more immediately after the dump | low | belt-and-braces; cheap, pairs well with B1 |

Recommended: **B1 + B4**. B1 removes the collision by construction; B4 makes
the property explicit so a future diagnostic cannot reintroduce it.

### Track C - harden EP0 against any residual latency

Independent of B, the firmware should not depend on being fast:

- Service EP0 **before** anything else in the poll loop, and service it for
  **both** controllers in one pass, so a long operation on dev0 cannot delay
  dev1's SETUP.
- Consider servicing EP0 SETUP directly in the ISR rather than the foreground
  loop. This is the structural fix - control-transfer response time stops being
  a function of main-loop cost entirely.

### Track D - only then revisit the test's actual intent

Hotplug cycling has **never executed once** in any round described in the
README (`dev0_cycles=0` throughout). Every constant tuned for it -
`DEV0_DISCONNECT_HOLD_US`, `PORT_POLL_*`, `PRE/POST_BULK_OUT_SETTLE` - is
currently **unvalidated**. Expect a second round of real debug *after* B
lands and DEV1 stays up. Do not tune those now; there is no data behind them.

---

## 4. Waveform checkpoints (you have the FSDB)

`novas.fsdb` / `vcs_dump.fsdb`. Window **680-700 us**. These are ordered to
confirm/refute the diagnosis above in one pass.

### W1 - confirm the MCU is stalled in `printf`, not in USB logic
Probe the MCU instruction/PC bus and `SOC_MCI_TOP_MCI_REG_DEBUG_OUT` writes
over 693.0-698.4 us.
**Expect:** a dense burst of ~184 single-byte stores to `DEBUG_OUT`, with the PC
parked in the `printf`/`VPRINTF` region for the whole 5.3 us.
**If instead** the PC is in `usb_ep1_confirm_armed()` spinning to its 1000-read
limit, the blocking agent is that spin, not the dump - re-aim Track B at it.

### W2 - confirm the SETUP arrived and was ignored
```
caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound  (dev1 instance)
  -> DEVCMDSTAT bit 8 (SETUP)
```
**Expect:** rises ~685.6 us (host's GET_DESCRIPTOR SETUP), stays high through
693.08 us (matching `DEVCMDSTAT=0x10814B83`), falls only ~698.35 us when
firmware finally decodes it. A ~12.7 us high time is the smoking gun.

### W3 - confirm EP0 OUT stayed correctly armed
Watch the dev1 EP0 OUT list entry in packet SRAM (offset 0x000) across
680-700 us.
**Expect:** constant `0x80004005`. Any transition to `0x80000005` would
resurrect the `NBytes` decay theory - the log says it does not happen.

### W4 - confirm the NAKs are device-sourced and SETUP-directed
Probe the dev1 UTMI/PHY handshake output around 692.78 / 693.93 / 695.23 us
(the three UVM_ERROR timestamps).
**Expect:** device-driven NAK PIDs responding to host SETUP tokens.

### W5 - confirm DEV1 isolation was never actually exercised
```
u_hub_compound.DEV0_USBREG_DEV_CONNECT
u_hub_compound.hub_port_reset[0]
u_hub_compound.hub_port_reset[1]
```
**Expect:** `DEV0_USBREG_DEV_CONNECT` **never toggles** after initial connect,
and `hub_port_reset[1]` is quiet after 570 us. Confirms `hp_state=0` forever and
that no isolation claim in the README has been validated yet.

---

## 5. Re-run instrumentation

Add to the firmware for the next iteration (cheap, and it closes the remaining
ambiguity):

- Count SETUPs **observed** (`DEVCMDSTAT.SETUP` seen set) vs SETUPs
  **serviced**. Any divergence is the latency bug, directly measured.
- Record max observed `mcycle` delta between consecutive poll-loop iterations,
  and print it **once at the end**. That turns "is the loop too slow?" into a
  single number instead of an inference.
- Print the verdict line unconditionally at the end (it is currently absent
  from this run's log entirely, because the loop exited on budget and the
  halt/objection path raced it).

---

## 6. Summary

| | |
|---|---|
| **Visible error** | 3x `valid_device_response_check_Dev3_EP0` (NAK to SETUP) |
| **Actual failure** | USBDC1 never configured; `dev0_cycles=0/3`; hotplug never ran |
| **Root cause** | ~184-char in-loop `VPRINTF` progress dump blocks EP0 SETUP service for ~5.3 us, deterministically colliding with USBDC1's enumeration |
| **Masking cause** | Host sequence ignores `svt_usb_transfer::status`; 4 ABORTED transfers produced 0 errors and a "enumeration complete" message |
| **Ruled out by log** | EP0 `NBytes` decay, round-8/9 deadlocks, EP1 `Active` livelock, `POST_PORT_RESET_SETTLE`, isolation violation |
| **Fix order** | A (make it fail honestly) -> B1+B4 (remove latency) -> C (harden EP0) -> D (then debug hotplug for real) |

---

## 7. Implemented (round 10) - A + B + C

All three tracks are now in the tree. Track D is deliberately **not** attempted
until a run shows `dev0_cycles > 0`.

### Track A - the test can now fail

| File | Change |
|---|---|
| `uvm/usb/caliptra_ss_usb_base_sequence.svh` | New `check_xfer_status(xfer, label, min_payload_bytes, out fail)`: errors on `null`, on `status != svt_usb_transfer::ACCEPT`, on any non-zero bit in `results_status`, and on `payload_byte_count() < min_payload_bytes`. New `wait_and_check_xfer(agent_h, label, min_payload_bytes, out fail)` = `wait_xfer_done()` + the above against `last_ctrl_seq_item`. |
| same | `usbdc0_enum_stepC()`: all 7 `wait_xfer_done()` calls replaced by `wait_and_check_xfer()` with per-step payload minimums - `GET_DESC_DEV` 18, `GET_STATUS` 2, `GET_CONFIG` 1, `SET_ADDRESS` / `SET_CONFIG` 0. The post-`SET_ADDRESS` descriptor read now only feeds `check_device_address()` when its own check passed. |
| `uvm/usb/caliptra_ss_usb_data_check_api_impl.svh` | `check_device_address()` gained two early-return `uvm_error` guards *before* the `hdl_path` select: non-`ACCEPT`/non-zero `results_status`, and zero `payload_byte_count()`. This is the line that previously printed `dev1 device address checked (expected=3 got=3)` on an ABORTED, empty transfer. |

`wait_xfer_done()` itself is unchanged and still used by the hub bring-up steps.

### Track B - the dump can no longer break the protocol

In `caliptra_ss_usb_dual_device_hs_dev0_hotplug.c`, the progress dump now
requires **all four** conditions:

```c
if (csr_read_mcycle() >= next_dump
    && dev0_cycle_count > 0u
    && !usb_ep0_setup_pending(0)
    && !usb_ep0_setup_pending(1)) {
```

* `dev0_cycle_count > 0` (B1) - silent through all enumeration.
* `!usb_ep0_setup_pending(dev)` (B4, new helper) - silent through the USBDC0
  re-enumeration that follows every reconnect.
* `next_dump` is **not** re-armed when deferring, so the cadence is not lost.

### Track C - EP0 serviced first, for both controllers

New `usb_service_ep0(int dev)` holds the former inline EP0 block verbatim
(SETUP -> `usb_handle_control_transfer()` + `usb_ep0_repair_out_nbytes()`;
else-if un-armed -> `usb_ep0_arm_out_sized()`), self-selects its controller, and
is idempotent. `main()` now opens every iteration with:

```c
usb_service_ep0(0);
usb_service_ep0(1);
usb_service_device(0, ev0, &dev_state[0]);
usb_service_device(1, ev1, &dev_state[1]);
```

`usb_service_device()` keeps its own `usb_service_ep0(dev)` call, which is a
no-op once the pass above has drained the SETUP. Branch order and the
unconditional SETUP check are preserved exactly - see the round-8 / round-9
notes in `README.md`.

### Falsifiable predictions for the next run

| Prediction | If it holds | If it fails |
|---|---|---|
| No `valid_device_response_check_Dev3_EP0` | latency was the whole story | there is a second, non-latency EP0 defect; next look at `ep0out` NBytes across the new, quieter log |
| `dev1 enumerated (addr=3)` appears | DEV1 control path is healthy | re-read the new Track A errors - they now name the exact failing transfer |
| `dev1 EP1 bulk loopback #1 complete` appears | EP1 path is healthy | EP1 handshake issue, independent of EP0 |
| `dev0_cycles` becomes non-zero | **first ever execution of the actual test** - Track D can begin | hotplug FSM / hold-time work is now legitimately debuggable |
| On a residual failure, first error is early (~685 us) | Track A is doing its job | Track A guard missed a path |

<!-- File contains AI-generated response based on internal company sources -->
