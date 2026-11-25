# caliptra_ss_usb_hs_dev_err_short_pkt

Truncates a High-Speed bulk OUT data packet to USBDC0 EP1.

## Coverage target

`usb_transfer_outcome_cg.cp_errortype` bin **`tr_eop` (0x8)** of
`src/usb/coverage/usb_dev_ep_cov.sv`, assigned at `usb_pie.m.vhdl`, four assignment sites.

The bin was at zero before this test existed, because nothing in the
regression ever produced a protocol error on a device endpoint.

## Mechanism

Host-side `svt_usb_packet_exception` with
`error_kind == LENGTH_ERROR` and `length_error == SHORT_PACKET_ERROR`. The
EOP arrives earlier than the declared length, which is what the TR_EOP name
records.

The firmware reports the residual byte count of the EP1 descriptor rather
than checking the payload, which makes a short packet directly visible in the
log.

## Status

**Confirmed unreachable.** The hub designer confirmed this limitation: a
short packet's CRC16 is recomputed over the truncated payload, so the result
is a structurally valid, correctly-CRC'd packet that simply ends early. A
short EOP is therefore never distinguishable from a normal end of transfer,
and `pie_errortype` can never be driven to TR_EOP (0x8) by this stimulus.

The test instead reports `0xf (DATA_IGNORED_WRONG_DATA01)`, for a reason
downstream of the same limitation rather than a separate bug: the DUT accepts
the short packet as a legitimate completed transfer (confirmed in the log by
`MCU: EP1 OUT completion 1 - received 1020 bytes (residual 4)`), which
silently advances the DUT's own data-toggle expectation to DATA0. The VIP
sequencer that drives the shared `do_clean_reference_xfer()` post_clean leg
never observed that acceptance - the injected packet was sent with a manually
pinned PID, bypassing the VIP's own toggle bookkeeping entirely - so its next
managed transfer still sends DATA1, which now collides with the DUT's
already-advanced DATA0 expectation and is reported as `0xf`. This is the same
toggle-mismatch mechanism exploited deliberately by `caliptra_ss_usb_hs_dev_err_toggle`,
occurring here as an unintended side effect of the DUT consuming the short
packet rather than rejecting it.

No testbench fix is possible: there is no PID value for the injected packet
that both triggers the length error and keeps the VIP's internal toggle state
consistent with a DUT that will legitimately consume the packet.

## Run


```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_short_pkt_test
```

## Where the detail lives

The RTL derivation of the 16 `pie_errortype` codes, the verified SVT VIP
exception field model, the list of codes that were removed from collection as
unreachable, and the reason the corrupted transfer is expected to fail are all
documented once in **`docs/CaliptraSSUSBErrorInjection.md`**. This family of
nine tests shares all of it; only the table above is specific to this suite.

Per-file detail:

- sequence header - why this particular bin needs this particular stimulus
- `caliptra_ss_usb_err_inject_base_sequence.svh` - shared helpers and the
  full code legend
- firmware `.c` / `libs/usb/usb_err_inject_fw_common.h` - the endpoint
  arming policy

<!-- File contains AI-generated response based on internal company sources -->
