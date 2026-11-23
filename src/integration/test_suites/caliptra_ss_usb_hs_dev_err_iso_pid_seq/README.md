# caliptra_ss_usb_hs_dev_err_iso_pid_seq

Out-of-sequence MDATA PID on a single-buffer isochronous OUT endpoint on
USBDC0, High Speed.

## Coverage target

`usb_transfer_outcome_cg.cp_errortype` bin `pid_unknown` (0x2), RTL site
`usb_pie.m.vhdl` line 2632 (`USB_PROT_OUT_SETUP_WF_RX_DATA_PID`, the
`iso_out_pending_r = '1'` case statement, `PID_MDATA` branch, taken when
`iso_transact_cnt_down = '00'`).

## Why MDATA is always unexpected here

MDATA is legal only on a HIGH-BANDWIDTH isochronous endpoint (USB 2.0 section
5.9.2): one that can carry up to 3 x 1024-byte transactions per microframe
(OUT: MDATA, MDATA, DATA2). `iso_transact_cnt_down` is loaded from
`epinfo_nbytes(11 downto 10)` when the first OUT data packet of a fresh
transfer is accepted (`usb_pie.m.vhdl` line ~3911). This test's EP2 OUT
endpoint uses a single-entry NBYTES descriptor with NO high-bandwidth setup,
so the intent is for `iso_transact_cnt_down` to load to `"00"` (single
transaction) on that first packet.

NBYTES has to be chosen carefully to get there: NBYTES=1024
(`epinfo_nbytes = "010000000000"`) has bits `[11:10] = "01"`, which lands in
the TWO-transaction high-bandwidth bucket instead - PID_MDATA is then legal
as the first of two HBW transactions and `pid_unknown` never fires. The
firmware therefore arms the endpoint for 1023 bytes instead
(`epinfo_nbytes = "001111111111"`, bits `[11:10] = "00"`), which is the
single-transaction case the test is modeling. The MDATA packet's PID is
checked before any payload byte is consumed, so the sequence's 1024-byte
MDATA payload is unaffected by the one-byte-smaller armed buffer.


## Why a directed packet sequence, not the transfer sequencer

The VIP's `svt_usb_transfer` API has no way to request an MDATA data PID on a
non-high-bandwidth endpoint - it only emits that PID when the endpoint's
`isoc_mult` is configured for high-bandwidth operation (see
`src/usb/tb/sequences/usb_high_bandwidth_iso_seq.svh`). This test instead
drives a directed OUT token and a bare MDATA data packet on the packet
sequencer, using `caliptra_ss_usb_err_inject_packet_sequence`.

## Shared-helper extension required and made

`caliptra_ss_usb_err_inject_packet_sequence`'s `pid`-to-`pid_type` case
statement only recognized `DATA0`/`DATA1` as `pid_type DATA`. Extended to also
accept `svt_usb_packet::MDATA` and `svt_usb_packet::DATA2`, following the
precedent already set in
`caliptra_ss_usb_ocp_packet_observer_selftest_sequence.svh`'s synthetic packet
builder. This is backward compatible: the new case arms are additional,
existing callers (`DATA0`/`DATA1`) are untouched.

## Stimulus split

- **Firmware** (`caliptra_ss_usb_hs_dev_err_iso_pid_seq.c`): arms EP2 OUT as
  isochronous (`USB_EP_ENTRY_TYPE_PERIODIC | USB_EP_ENTRY_RF_ISO`), single
  buffer entry, exactly once, then only services EP0 until the host's STOP
  handshake.
- **Sequence** (`caliptra_ss_usb_hs_dev_err_iso_pid_seq_sequence.svh`): sends a
  directed OUT token to EP2, then a bare MDATA data packet (no exception
  attached - MDATA is a legal, well formed PID; the error is purely
  sequencing).

## Expected outcome

No handshake at all: isochronous transfers never carry one (USB 2.0 section
8.5.5), and the RTL branch additionally returns the FSM to WF_IDLE without
reaching a DMA/ACK step. The coverage bin closing is the evidence. If the
firmware instead logs an "UNEXPECTED EP2 OUT (ISO) completion", the RTL
accepted the MDATA packet as ordinary data and the bin did not close.

## Suppressed VIP check

`tend_to_end_delay_check` (LINK 20 TIMING CHECKS:COMMON) is set to
`svt_err_check_stats::EXPECTED` in `end_of_elaboration_phase` of
`caliptra_ss_usb_hs_dev_err_iso_pid_seq_test.svh`. The injected MDATA packet
is, by design, never answered (see "Expected outcome" above), and the VIP
link layer starts its End-to-end Signal Delay timer on it regardless. Same
suppression API and precedent as `caliptra_ss_usb_hs_dev_err_toggle_test`,
which documents the full rationale.

## Line 2704 is not closed by this suite

usb_pie.m.vhdl line 2704 (`PID_DATA0` unexpected when `iso_mdata_cnt_up /=
"00"`) is NOT reachable on this endpoint: `iso_mdata_cnt_up` only increments
on an *accepted* MDATA, which requires a high-bandwidth endpoint - the
opposite of this suite's deliberately single-buffer, non-HBW configuration.
Rather than risk this suite's three already-closed lines
(2632/2655/2680) by changing the endpoint config in place, line 2704 is
closed by a separate, forked sibling suite,
`caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw`, which arms a true
high-bandwidth endpoint and sends a legitimate MDATA before the mismatching
DATA0. See that suite's README for details.

## Usage

```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_iso_pid_seq_test
+usb_errortype_check=1
+usb_errortype_check_sel=1
+usb_expect_errortype=2
```


<!-- File contains AI-generated response based on internal company sources -->
