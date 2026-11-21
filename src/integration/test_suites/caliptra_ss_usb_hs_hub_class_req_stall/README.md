# caliptra_ss_usb_hs_hub_class_req_stall

Hub **class-request STALL decode** test for the USB 2.0 compound device
(embedded virtual hub + two software device controllers), running at
**High Speed**.

Stimulus for the hub half of coverage gap **G9** of `docs/usb_coverage_gaps.md`
("STALL / halt paths in DMA and hub").

## Intent

`usb_app_hw_hub` rejects unsupported hub class requests by asserting
`ep0_class_stall`, which makes the hub answer the SETUP with a STALL handshake.
That decode had never been driven. `C_HUB_NB_PORTS = 2` in this integration and
every existing hub test addresses `wIndex` 0 or 1 with legal feature selectors
only (`0x0002`, `0x0004`, `0x0010`, `0x0012`, `0x0014`), so no test ever produced
an out-of-range port number or an out-of-list `wValue` at the hub.

The STALL that *is* already covered is a different one:
`caliptra_ss_usb_hs_hub_test_mode` drives `SET_FEATURE(TEST_MODE)`, a
**STANDARD** request rejected inside the EP0 handler, not by this class decoder.

## What is checked

Six unsupported requests, each of which must be **STALLed**, followed by one
legal request that must **complete**.

| # | Request | wIndex | wValue | Expected | RTL condition |
|---|---|---|---|---|---|
| 3 | ClearPortFeature | 3 | `C_PORT_CONNECTION` (16) | STALL | `wIndex[7:0] > C_HUB_NB_PORTS` (line 103) |
| 4 | ClearPortFeature | 1 | 5 | STALL | `wValue` not in the Clear list (line 125) |
| 5 | SetPortFeature | 3 | `PORT_RESET` (4) | STALL | `wIndex[7:0] > C_HUB_NB_PORTS` (line 138) |
| 6 | SetPortFeature | 1 | `PORT_L1` (10) | STALL | `wValue` not in the Set list (line 158) |
| 7 | GetPortStatus | 3 | 0 | STALL | `wIndex[15:0] > C_HUB_NB_PORTS` (line 133) |
| 8 | SetAndTestPortFeature | 0 | `PORT_L1` (10) | STALL | `wIndex[3:0] = 0` (lines 165-168) |
| 9 | GetPortStatus | 1 | 0 | **completes** | a supported request must not stall |

Line numbers are in
`third_party/usb2/src/usb_hub_composite_device/RTL/RTL/usb_app_hw_hub.m.vhdl`.

Step 9 is the control leg and is not decoration: six consecutive STALLs would
also be satisfied by an EP0 that had simply stopped answering. It additionally
reports `wPortChange`, so a rejected request that had nevertheless disturbed the
port would be visible.

## Why these all fit in one test (MEASURED)

`PROC_CLASS_STALL` (lines 96-177) is **purely combinational** on `ep0_request`,
`ep0_setupdone`, `ep0_windex` and `ep0_wvalue`, and its only output is
`ep0_class_stall`.

The matching arms in the sequential `PROC_REQUEST_HANDLING` are explicit
no-ops, so **every leg leaves the hub's state completely untouched**:

```vhdl
-- ClearPortFeature, bad port (213-214)
if to_integer(unsigned(ep0_windex(7 downto 0))) > C_HUB_NB_PORTS then
  null; -- A stall will be returned upon this request

-- SetPortFeature, bad port (258-259)
  null; -- A stall will be returned upon this request

-- GetPortStatus (253): data_index is only latched for a legal port
if to_integer(unsigned(ep0_windex(15 downto 0))) <= C_HUB_NB_PORTS then
  data_index <= to_integer(unsigned(ep0_windex));

-- bad wValue (247-248, 285-286)
when others => null;
```

No port enable / suspend / reset / change bit moves, no `data_index` update and
no bus reset. The legs are therefore order-free and cannot interfere with each
other, which is why they are grouped. This is the opposite of
`caliptra_ss_usb_hs_hub_int_ep_status_change`, where
`SetPortFeature(PORT_RESET)` bus-resets USBDC0 and forces a step order.

## Why `wValue = 10` for the SetPortFeature bad-value leg

The two accepted-`wValue` lists are deliberately different:

| wValue | ClearPortFeature (105-126) | SetPortFeature (140-159) |
|---|---|---|
| 10 `PORT_L1` | accepted (line 113) | **STALL** |
| 23 `C_PORT_L1` | accepted (line 121) | **STALL** |
| 5, 6, 7, 11-15, 24+ | STALL | STALL |

Using 10 on the Set leg proves the Set decoder carries its own selector list,
which a generic out-of-range value such as 5 would not. The Clear leg uses 5,
which is unlisted for both.

## How a STALL is observed

Same mechanism as `caliptra_ss_usb_hs_hub_test_mode_sequence`: the VIP reports a
control transfer terminated by a device STALL handshake as
`svt_sequence_item::ABORTED` on `last_ctrl_seq_item`. `check_setup_stalled()` in
the sequence is that same check, generalised over a label, and it carries a
`why_text` naming the RTL condition so a failure says which decode arm
misbehaved rather than only that a transfer outcome was unexpected.

A null `last_ctrl_seq_item` is `uvm_fatal`, so a refactor that drops the cast
cannot silently turn the check into a no-op.

## Why the MCU firmware does nothing special

The decode is combinational hardware with no firmware path, so
`caliptra_ss_usb_hs_hub_class_req_stall.c` is the standard bring-up plus the EP0
poll loop that keeps USBDC0 responsive while the host enumerates the hub - the
same loop as `caliptra_ss_usb_hs_hub_endpoint_halt`. `USB_POLL_TIMEOUT` is 5000,
matching that test; the sequence is nine EP0 control transfers with no data
phase longer than four bytes, so it finishes well inside that budget.

No MCU STOP handshake is used here. That mechanism exists in
`caliptra_ss_usb_hs_hub_int_ep_status_change` because that test's firmware had
to stay alive through long interrupt-IN polls; this one does not.

## Side effects

None. Every request in the sequence is either rejected before it can change
state, or is a read. The downstream ports are deliberately never brought up:
each leg is decoded from the SETUP fields alone.

## Status - first run (MEASURED)

**PASS.** `UVM_ERROR : 0`, `UVM_FATAL : 0`, `UVM_WARNING : 0`, quit count 0 of 150.

All six stall legs returned a STALL handshake on the first SETUP, and the legal
leg completed:

| # | Leg | Issued (ns) | Outcome (ns) | Result |
|---|---|---|---|---|
| 3 | `ClearPortFeature_badPort` wValue 0x0010 wIndex 0x0003 | 362706 | 364275 | stalled, `ABORTED` |
| 4 | `ClearPortFeature_badValue` wValue 0x0005 wIndex 0x0001 | 364275 | 365708 | stalled, `ABORTED` |
| 5 | `SetPortFeature_badPort` wValue 0x0004 wIndex 0x0003 | 365708 | 367142 | stalled, `ABORTED` |
| 6 | `SetPortFeature_badValue` wValue 0x000a wIndex 0x0001 | 367142 | 368542 | stalled, `ABORTED` |
| 7 | `GetPortStatus_badPort` wIndex 0x0003 | 368542 | 370008 | stalled, `ABORTED` |
| 8 | `SetAndTestPortFeature_port0` wValue 0x000a wIndex 0x0000 | 370008 | 371475 | stalled, `ABORTED` |
| 9 | `GetPortStatus_valid` wIndex 0x0001 | 371475 | 374041 | completed, `ACCEPT` |

Corroborating evidence:

* `env.host_agent.link_mon.20.RX.pkt_trace` shows exactly **six**
  `HANDSHAKE / STALL` packets, at 364272.9, 365706.2, 367139.5, 368539.4,
  370006.0 and 371472.6 ns - one per stalled leg and none elsewhere.
* Step 9 returned the 4-byte status word `0x00010501` (`wPortStatus 0x0501`,
  `wPortChange 0x0001`), so EP0 is not wedged after six consecutive STALLs and
  port 1 was not disturbed by the rejected requests.
* `mcu_console.log` ends with
  `USB hub class-request STALL test - transfers handled: 0`, confirming the
  firmware took no part in the decode - every STALL came from the hub hardware.

## Files

| File | Note |
|---|---|
| `caliptra_ss_usb_hs_hub_class_req_stall.c` | MCU firmware: standard hub bring-up plus the EP0 poll loop. Takes no part in the decode under test. |
| `caliptra_ss_usb_hs_hub_class_req_stall.yml` | Test entry, `+UVM_TESTNAME=caliptra_ss_usb_hs_hub_class_req_stall_test` |
| `cptra_bringup.c` | symlink to `../libs/usb/bringup/cptra_bringup.c` |
| `.../uvm/usb/caliptra_ss_usb_hs_hub_class_req_stall_sequence.svh` | Host sequence, nine steps |
| `.../uvm/usb/caliptra_ss_usb_hs_hub_class_req_stall_test.svh` | Test class: HS speed only, no endpoint overrides needed |

## Notes for whoever picks this up

* The test class sets **only** the speed. The sequence is EP0-only, so no
  endpoint model beyond the shared CONTROL entry is needed, and the shared NAK
  retry budget is irrelevant - a STALLed control transfer terminates on the
  STALL handshake, not by exhausting retries.
* `bmRequestType` recipient is `BMREQ_OTHER` on every leg, which is what
  addresses a downstream **port** rather than the hub itself. Changing it to
  `BMREQ_DEVICE` would change which request the hub decodes and would silently
  invalidate the port-number legs.
* `PORT_BAD = 3` is the first illegal port number for `C_HUB_NB_PORTS = 2`. If
  the hub is ever reconfigured with more ports, `PORT_BAD` and `HUB_NB_PORTS` in
  the sequence must move together.
* `GetPortStatus` compares the **full** `wIndex[15:0]` (line 133) while
  Set/ClearPortFeature compare only `wIndex[7:0]` (lines 138 / 103) and
  `SetAndTestPortFeature` only `wIndex[3:0]` (lines 165-168). The three widths
  are genuinely different in the RTL; do not "unify" the legs.
* UVM output goes to `svt_debug.transcript`, not `vcs_sim.log`, when the SVT
  transcript is enabled. Use
  `grep -E "=== STEP|USB_HUB_CLASS_STALL" svt_debug.transcript` to follow the
  test.
* The `.c` file's IDE errors (`incomplete type "enum printf_verbosity"`,
  `identifier "LOW" is undefined`) are include-path artefacts present in every
  USB test `.c` and must NOT be "fixed".

<!-- File contains AI-generated response based on internal company sources -->
