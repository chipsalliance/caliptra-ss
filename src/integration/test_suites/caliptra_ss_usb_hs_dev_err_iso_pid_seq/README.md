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
(OUT: MDATA, MDATA, DATA2). `iso_transact_cnt_down` is loaded from epinfo when
the first OUT data packet of a fresh transfer is accepted. This test's EP2 OUT
endpoint is the same single 1024-byte-buffer configuration
`caliptra_ss_usb_hs_dev_err_pkt_unexpected` / `err_iso_stalled` already use -
one NBYTES entry, no high-bandwidth setup - so `iso_transact_cnt_down` loads
to `"00"` (single transaction) on that first packet. Sending MDATA as that
first data packet therefore always hits the `iso_transact_cnt_down = '00'`
branch and reports `ERROR_PID_UNKNOWN`.

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

## Usage

```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_iso_pid_seq_test
+usb_errortype_check=1
+usb_errortype_check_sel=1
+usb_expect_errortype=2
```

<!-- File contains AI-generated response based on internal company sources -->
