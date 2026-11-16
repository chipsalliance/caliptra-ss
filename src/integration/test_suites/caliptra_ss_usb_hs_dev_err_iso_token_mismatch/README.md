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

## Stimulus

- **Firmware** (`caliptra_ss_usb_hs_dev_err_iso_token_mismatch.c`): arms EP2
  OUT as isochronous (`USB_EP_ENTRY_TYPE_PERIODIC | USB_EP_ENTRY_RF_ISO`),
  re-arming it after each normal ISO OUT data-phase completion so the
  sequence's three OUT data phases each land on a fresh buffer. There is no
  firmware-side reaction to the mismatched tokens themselves - all four
  target RTL branches return the FSM to `WF_IDLE` without any DMA/interrupt.
- **Sequence** (`caliptra_ss_usb_hs_dev_err_iso_token_mismatch_sequence.svh`):
  1. Sends an ISO OUT data phase (`do_data_xfer` with `single_isoc_txn=1`,
     the same pattern `caliptra_ss_usb_hs_dev_iso_out_sequence` uses) to arm
     `iso_out_pending_r = '1'`, then sends a directed `PID_IN` token (line
     2192).
  2. Repeats the ISO OUT arm, then sends a directed `PID_SETUP` token
     (line 2231).
  3. Repeats the ISO OUT arm, then sends a directed `PID_PING` token
     (line 2251).
  4. Sends a directed `PID_IN` token (to set `iso_in_pending_r`), then a
     directed `PID_OUT` token (line 2211).
  All tokens are driven via `caliptra_ss_usb_err_inject_packet_sequence` on
  the packet sequencer with `attach_exception=0` - every token is legal and
  well formed; the error is purely about **when** it arrives, not how it is
  built. This is the same "sequencing error" category as
  `caliptra_ss_usb_hs_dev_err_iso_pid_seq` and
  `caliptra_ss_usb_hs_dev_err_toggle`.

## No exception, no handshake

No `svt_usb_packet_exception` is attached to any packet. Isochronous
transfers carry no handshake at all (USB 2.0 section 8.5.5), and every one
of the four target branches ends in `set_pie_endtransfer`/
`clear_pie_success` with no DMA/ACK step reached, so none of the directed
tokens in this sequence is ever answered. The evidence is the coverage bin
and the RTL line hits, not a protocol-level pass/fail check.

## Usage

```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_iso_token_mismatch_test
+usb_errortype_check=1
+usb_errortype_check_sel=1
+usb_expect_errortype=3
```

# File contains AI-generated response based on internal company sources
