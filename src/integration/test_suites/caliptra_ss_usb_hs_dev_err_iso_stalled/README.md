# caliptra_ss_usb_hs_dev_err_iso_stalled

Isochronous OUT data packet to a STALLed endpoint on USBDC0, High Speed.

## Coverage target

`usb_transfer_outcome_cg.cp_errortype` bin `packet_unexpected` (0x3), RTL site
`usb_pie.m.vhdl` line 2837 (`USB_PROT_OUT_SETUP_RCV_DATA_PACKET`, the
`epinfo_stall = '1' and epinfo_active = '0'` branch taken when
`iso_out_pending_r = '1'`).

This is distinct from the site `caliptra_ss_usb_hs_dev_err_pkt_unexpected`
already closes (line 2879, `ACTIVE` clear but `STALL` not set), and distinct
from the bulk-endpoint STALL sites `caliptra_ss_usb_hs_dev_err_stall` closes
(lines 2391/2816): line 2837 needs an isochronous endpoint with BOTH `STALL`
set and `ACTIVE` clear.

## Why this test is firmware driven

`epinfo_stall` and `epinfo_active` are latched straight out of the EP2 OUT
command/status list entry (`USB_EP_ENTRY_STALL` / `USB_EP_ENTRY_ACTIVE`), so
only firmware can produce the condition. No `svt_usb_packet_exception` is
used - the ISO OUT data packet is sent exactly as built.

## Stimulus split

- **Firmware** (`caliptra_ss_usb_hs_dev_err_iso_stalled.c`): arms EP2 OUT as
  isochronous (`USB_EP_ENTRY_TYPE_PERIODIC | USB_EP_ENTRY_RF_ISO`) with
  `STALL` set and `ACTIVE` clear, as soon as the control pipe is running.
  Never re-arms it; deliberately no EP2 OUT completion handling.
- **Sequence** (`caliptra_ss_usb_hs_dev_err_iso_stalled_sequence.svh`): sends
  one 1024-byte isochronous OUT transfer to EP2.

## Expected outcome

No handshake at all (USB 2.0 section 8.5.5 - isochronous transfers carry no
handshake), so the transfer itself is not status-checked. The coverage bin
closing is the evidence. There is no recovery leg: the endpoint stays halted
by design, same as `caliptra_ss_usb_hs_dev_err_stall`.

## Usage

```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_iso_stalled_test
+usb_errortype_check=1
+usb_errortype_check_sel=1
+usb_expect_errortype=3
```

<!-- File contains AI-generated response based on internal company sources -->
