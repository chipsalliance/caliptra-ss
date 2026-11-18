# caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw

Out-of-sequence DATA0 PID on a high-bandwidth (HBW) isochronous OUT endpoint
on USBDC0, High Speed.

## Forked from caliptra_ss_usb_hs_dev_err_iso_pid_seq, not an edit to it

`caliptra_ss_usb_hs_dev_err_iso_pid_seq` deliberately uses a single-buffer,
non-high-bandwidth endpoint (NBYTES=1023, bits `[11:10]="00"`) to close
`usb_pie.m.vhdl` lines 2632/2655/2680 - see that suite's README. Line 2704
(`PID_DATA0` unexpected when `iso_mdata_cnt_up /= "00"`) can only be reached
on a HIGH-BANDWIDTH endpoint, since `iso_mdata_cnt_up` only increments on an
accepted MDATA, which itself requires `iso_transact_cnt_down /= "00"` at load
time - the opposite endpoint configuration. Changing the existing suite's
endpoint config in place would risk regressing its already-closed
2632/2655/2680 coverage, so this is a new, standalone sibling test instead -
no code in the original suite is touched.

## Coverage target

`usb_transfer_outcome_cg.cp_errortype` bin `pid_unknown` (0x2), RTL site
`usb_pie.m.vhdl` line 2704 (`USB_PROT_OUT_SETUP_WF_RX_DATA_PID`, the
`iso_out_pending_r = '1'` case statement, `PID_DATA0` branch, taken when
`iso_mdata_cnt_up /= "00"`). This test adds no new BIN coverage (`pid_unknown`
is already closed by the sibling suite); its only purpose is the RTL
line/branch hit at 2704.

## Why the first data phase must be a legitimate MDATA

`iso_mdata_cnt_up` starts at `"00"` on a fresh transfer and only increments on
an ACCEPTED MDATA (`incr_iso_mdata_cnt_up`). So reaching line 2704's guard
(`iso_mdata_cnt_up /= "00"`) requires a first, legitimate MDATA data phase to
be accepted before the mismatching DATA0 is sent. On this high-bandwidth
endpoint (NBYTES bits `[11:10]="10"`, loaded by the firmware), that first
MDATA is legal and IS accepted (`usb_pie.m.vhdl` line 2632's guard,
`iso_transact_cnt_down = 00 or iso_mdata_cnt_up = 10`, is false on the first
packet), so it reaches the normal DMA handoff and the firmware sees one EP2
OUT completion for it.

## Why a directed packet sequence, not the transfer sequencer

Same reasoning as the non-HBW sibling: the VIP's `svt_usb_transfer` API only
emits MDATA when `isoc_mult` is configured for true high-bandwidth operation
end-to-end (`src/usb/tb/sequences/usb_high_bandwidth_iso_seq.svh`), and it has
no way to send a bare DATA0 packet out of sequence at all. Both data phases
are therefore driven directly on the packet sequencer via
`caliptra_ss_usb_err_inject_packet_sequence`, each preceded by its own
directed OUT token.

## Stimulus split

- **Firmware** (`caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw.c`): arms EP2 OUT
  as a high-bandwidth isochronous endpoint (`USB_EP_ENTRY_TYPE_PERIODIC |
  USB_EP_ENTRY_RF_ISO`, NBYTES=2048, bits `[11:10]="10"`), re-arming it after
  the first (legitimate) data phase completes.
- **Sequence** (`caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw_sequence.svh`):
  1. Directed OUT token + legitimate MDATA data phase - accepted, sets
     `iso_mdata_cnt_up` to `"01"`.
  2. Directed OUT token + mismatching DATA0 data phase (line 2704).

All packets are driven with `attach_exception=0` - every packet is legal and
well formed; the error is purely sequencing (DATA0 where MDATA/DATA1 is
expected).

## Expected outcome

The mismatching DATA0 gets no handshake at all: isochronous transfers never
carry one (USB 2.0 section 8.5.5), and the RTL branch additionally clears
the ISO pending flags and returns the FSM to WF_IDLE without reaching a
DMA/ACK step. The firmware logs each EP2 OUT completion it does see; more
than one completion is the signal that the DATA0 was (incorrectly) accepted
as ordinary data and the bin did not close at this site.

## Suppressed VIP check

`tend_to_end_delay_check` (LINK 20 TIMING CHECKS:COMMON) is set to
`svt_err_check_stats::EXPECTED` in `end_of_elaboration_phase` of
`caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw_test.svh`, same precedent as the
non-HBW sibling.

## Usage

```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw_test
+usb_errortype_check=1
+usb_errortype_check_sel=1
+usb_expect_errortype=2
```

<!-- File contains AI-generated response based on internal company sources -->
