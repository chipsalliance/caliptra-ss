# caliptra_ss_usb_hs_dev_err_iso_token_mismatch

## Coverage target

`usb_transfer_outcome_cg.cp_errortype` bin `packet_unexpected` (0x3) -
the **same bin** `caliptra_ss_usb_hs_dev_err_pkt_unexpected` and
`caliptra_ss_usb_hs_dev_err_iso_stalled` already close. This test adds **no
new bin-level coverage**. Its value is RTL **line/branch** coverage of four
specific dark assignment sites in `usb_pie.m.vhdl`:

| Line | Branch | Condition |
|------|--------|-----------|
| 2192 | `PID_IN` in `USB_PROT_WF_TOKEN_BYTE3` | `iso_out_pending_r = '1'` ("PID_OUT was expected") |
| 2211 | `PID_OUT` in `USB_PROT_WF_TOKEN_BYTE3` | `iso_in_pending_r = '1'` ("PID_IN was expected") |
| 2231 | `PID_SETUP` in `USB_PROT_WF_TOKEN_BYTE3` | either iso pending flag set |
| 2251 | `PID_PING` in `USB_PROT_WF_TOKEN_BYTE3` | either iso pending flag set |

`caliptra_ss_usb_hs_dev_err_pkt_unexpected`'s own sequence header documents
all seven live 0x3 assignment sites in the RTL
(2192/2211/2231/2251/2295/2837/2879) and explicitly targets only 2879
(endpoint `ACTIVE` clear); `err_iso_stalled` targets 2837 (endpoint
`STALL`ed). Neither probes the four "token arrives while an ISO transaction
is pending" branches this test targets.

## Why no new bin coverage, and why implement it anyway

The decision to implement this test despite it closing an already-closed
bin was made explicitly after confirming (during coverage-completeness
review of this error-injection test family) that a full regression pass of
all existing tests still leaves these four RTL lines dark. Closing them
requires racing a directed token against the DUT's internal
`iso_out_pending_r`/`iso_in_pending_r` state - a scenario neither of the two
existing 0x3 tests happens to construct.

## Root cause of the original (superseded) design's failure

An earlier version of this test armed `iso_out_pending_r`/`iso_in_pending_r`
with an ordinary **single-transaction** (non-high-bandwidth, `NBYTES` bits
`[11:10]="00"`) isochronous transfer, using `do_data_xfer()` with
`single_isoc_txn=1`. `usb_pie.m.vhdl` clears `iso_out_pending_r`/
`iso_in_pending_r` as soon as `iso_transact_cnt_down` reaches `"00"` after a
transaction completes (`USB_PROT_OUT_SETUP_RCV_DATA_PACKET`'s CRC-valid
branch, ~line 2951, for OUT; `USB_PROT_IN_TX_CRC16_BYTE2`, ~line 3086, for
IN). For a single-transaction transfer that happens on the very first data
phase, so by the time the FSM returns to `USB_PROT_WF_TOKEN_BYTE3` waiting
for a new token, the pending flag has **already cleared** - the mismatched
token that followed could never land in the "unexpected" window. A full
RTL trace confirmed the test, as originally written, never actually hit any
of the four target lines; it only ever reached the generic `TIMEOUT`
(0x6)/`SENT_RECEIVED_NAK` (0x9) paths.

## The fix: both EP2 OUT and EP2 IN are 2-transaction HBW endpoints

**Firmware** (`caliptra_ss_usb_hs_dev_err_iso_token_mismatch.c`) now arms
both EP2 OUT and EP2 IN as single-descriptor, 2-transaction high-bandwidth
(HBW) isochronous endpoints (`USB_EP_ENTRY_TYPE_PERIODIC`, `NBYTES` bits
`[11:10]="01"`, i.e. `USB_EP2_NBYTES_HBW = 1536`), armed up front on the
first control transfer (both endpoints re-armed after each completion so
every leg starts fresh). With `iso_transact_cnt_down` loaded to `"01"`, it
only **decrements** (to `"00"`) when the first of the two transactions
completes - `iso_out_pending_r`/`iso_in_pending_r` stay asserted across the
token boundary, exactly the window the mismatched token needs. The test
completes only the first transaction of each endpoint, then substitutes a
mismatched token for what would have been the second transaction's token.

EP2 IN can now be armed alongside EP2 OUT from the start: the four target
`USB_PROT_WF_TOKEN_BYTE3` branches key only on
`iso_out_pending_r`/`iso_in_pending_r`, not on either endpoint's own arm
state, so there is no interaction between EP2 IN being active and the
PID_IN/PID_SETUP/PID_PING legs that target EP2 OUT's pending flag.

**Sequence** (`caliptra_ss_usb_hs_dev_err_iso_token_mismatch_sequence.svh`):

1. `arm_iso_out()`: a directed OUT token followed by a legitimate `PID_MDATA`
   data phase (1024 bytes), arming `iso_out_pending_r = '1'` while leaving it
   set, then a directed `PID_IN` mismatched token (line 2192).
2. Repeats `arm_iso_out()`, then a directed `PID_SETUP` mismatched token
   (line 2231).
3. Repeats `arm_iso_out()`, then a directed `PID_PING` mismatched token
   (line 2251).
4. `arm_iso_in()`: a bare directed IN token eliciting the DUT's own
   auto-generated first DATA response, arming `iso_in_pending_r = '1'`
   while leaving it set, then a directed `PID_OUT` mismatched token
   (line 2211).

All tokens/data phases are driven via `caliptra_ss_usb_err_inject_packet_sequence`
directly on the raw packet sequencer with `attach_exception=0` - every
packet is legal and well formed; the error is purely about **when** the
mismatched token arrives, not how it is built. This is the same "sequencing
error" category as `caliptra_ss_usb_hs_dev_err_iso_pid_seq` and
`caliptra_ss_usb_hs_dev_err_toggle`.

### Why the OUT-side arming data phase must be `PID_MDATA`

`usb_pie.m.vhdl`'s `USB_PROT_OUT_SETUP_WF_RX_DATA_PID` case statement (the
`iso_out_pending_r = '1'` branch, ~line 2646) requires the data PID to match
the current transaction count. With `iso_transact_cnt_down` loaded to
`"01"`, `PID_MDATA`'s guard (`iso_transact_cnt_down = "00" or
iso_mdata_cnt_up = "10"`) is false on the first packet, so MDATA is
**accepted** and increments `iso_mdata_cnt_up` to `"01"` **without**
clearing `iso_transact_cnt_down` - only the last-transaction branches
(DATA2/DATA1/DATA0) assert `clear_iso_transact_cnt_down`. At the subsequent
CRC-valid completion, `iso_transact_cnt_down` is still `"01"`, so the RTL
takes the `decr_iso_transact_cnt_down` branch rather than
`clear_iso_out_pending` - `iso_out_pending_r` survives for the mismatched
token. Any other PID on the first packet of a `"01"`-bucket transfer either
marks the transaction as the last one (reproducing the original bug) or is
rejected as `pid_unknown` (0x2), not the target `packet_unexpected` (0x3).

### Why the IN-side arming step needs no explicit data-PID construction

EP2 IN is device-to-host: the DUT itself selects the DATAx PID to transmit,
keyed directly on `iso_transact_cnt_down`
(`USB_PROT_IN_TX_DATA_PID_1`/`_2`, ~line 3010/3037) - `"00"`->DATA0,
`"01"`->DATA1, others->DATA2. A bare directed IN token is therefore enough
to elicit the DUT's own correctly-sequenced first response; at
`USB_PROT_IN_TX_CRC16_BYTE2` (~line 3086) the `"01"` count only decrements,
leaving `iso_in_pending_r = '1'` for the mismatched OUT token that follows.

## No exception, no handshake (on the mismatched tokens)

No `svt_usb_packet_exception` is attached to any of the four mismatched
tokens. Isochronous transfers carry no handshake at all (USB 2.0 section
8.5.5), and every one of the four target branches ends in
`set_pie_endtransfer`/`clear_pie_success` with no DMA/ACK step reached, so
none of the four mismatched tokens is ever answered with real transfer
data. The evidence is the coverage bin and the RTL line hits, not a
protocol-level pass/fail check.

## VIP self-checks relaxed in this test

Two SVT checks are deliberately demoted to `EXPECTED` in
`caliptra_ss_usb_hs_dev_err_iso_token_mismatch_test::end_of_elaboration_phase`
(same `chk_cov_mgr.find()` + `set_default_fail_effect()` API used throughout
this test family):

- `tend_to_end_delay_check` (`env.host_agent.link`): none of the four
  mismatched tokens is ever answered, so the VIP's end-to-end delay timer on
  them fires as an expected artifact.
- `rx_packet_routed_check` (`env.host_agent.prot`): all packets in this
  sequence - including the legitimate arming phases - are injected via
  `caliptra_ss_usb_err_inject_packet_sequence` directly on the raw packet
  sequencer, bypassing `do_data_xfer()`/`svt_usb_transfer` registration. The
  DUT still answers a bare directed token the normal way, and that response
  cannot be routed by the host-side PROTOCOL TRANSACTOR because no transfer
  was ever tracked for it. Confirmed via a regression run's
  `svt_debug.transcript` `report_xact` table, independent of endpoint arm
  timing.

## Usage

```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_iso_token_mismatch_test
+usb_errortype_check=1
+usb_errortype_check_sel=1
+usb_expect_errortype=3
```

# File contains AI-generated response based on internal company sources
