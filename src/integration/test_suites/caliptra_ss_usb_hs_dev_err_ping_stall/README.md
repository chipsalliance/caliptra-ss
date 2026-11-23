# caliptra_ss_usb_hs_dev_err_ping_stall

Sends a PING to a USBDC0 EP1 that the firmware has STALLed, at High Speed.

## Coverage target

`usb_transfer_outcome_cg.cp_errortype` bin **`sent_stall` (0xA)** of
`src/usb/coverage/usb_dev_ep_cov.sv`, assigned at `usb_pie.m.vhdl` line 2528
(`USB_PROT_PING_WF_EP_INFO_VALID`).

`caliptra_ss_usb_hs_dev_err_stall` already closes this same code at lines
2391/2816 (IN/OUT data to a stalled EP). This suite closes the PING-specific
site: PING has its own waiting states in the PIE
(`USB_PROT_PING_WF_EOP` / `USB_PROT_PING_WF_EP_INFO_VALID`) with their own
`errortype` assignment, so it is a separate live site from the IN/OUT ones.

## Mechanism

**No injection at all**, same as `err_stall`: the firmware arms EP1 OUT with
STALL set and ACTIVE clear. The only difference from `err_stall` is the host
stimulus - a single directed PING token (HS only) instead of a bulk OUT
transfer.

## One suppressed VIP check

Sending PING as a directed packet, with no preceding transfer-level context,
trips the VIP's own PROTOCOL TRANSACTOR self-check because it cannot attribute
the packet to a device:

```
[register_fail:PROTOCOL TRANSACTOR:IN-LINE:rx_packet_routed_check]
  Detect Unexpected Packet - Can't tell where this packet should go,
  No device with matching address found!
```

Confirmed from a real run: the errortype checker's own verdict closes the
sent_stall bin (pie_errortype = 0xa reported 5266 times, "PASS: ... bin is
closed") before this check fires, so it is a VIP self-check artifact riding
along with the directed-packet stimulus, not an injection or recovery failure.
`caliptra_ss_usb_hs_dev_err_ping_stall_test.svh` sets this one check to
`svt_err_check_stats::EXPECTED` in `end_of_elaboration_phase`, the same
pattern used by `err_toggle` and `err_long_pkt`.

## Run

```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_ping_stall_test
```


## Where the detail lives

The RTL derivation of the 16 `pie_errortype` codes, the verified SVT VIP
exception field model, and the reason the corrupted transfer is expected to
fail are documented once in **`docs/CaliptraSSUSBErrorInjection.md`**.

Per-file detail:

- sequence header - why this particular bin needs this particular stimulus
- firmware `.c` - the endpoint arming policy (same as `err_stall`)

<!-- File contains AI-generated response based on internal company sources -->
