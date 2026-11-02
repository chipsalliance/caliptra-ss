# caliptra_ss_usb_hs_dev_unsupported_ep

High-Speed directed test: a BULK OUT token is sent to an endpoint number that
has **no physical endpoint** behind it, and the device must not respond at all
(no ACK, no NAK, no STALL).

## Endpoint choice

`src/integration/rtl/caliptra_ss_top.sv` sets

```
parameter USB_C_DEV0_NBPHYSEP = 28;
parameter USB_C_DEV1_NBPHYSEP = 28;
```

which is forwarded to the compound wrapper as `C_DEV0_NBPHYSEP` /
`C_DEV1_NBPHYSEP` and from there to the per-device VHDL `C_NBPHYSEP` generic.
Physical endpoints come in OUT/IN pairs, so 28 slots back endpoint numbers
**1..14**. Endpoint **15** is therefore the first endpoint number with no
physical endpoint, and it is also the largest value the RTL `t_ep.EPNB`
(`range 0 to 15`) can encode, which makes it the natural probe target.

## Structure

- Host VIP (UVM): enumerates the hub and USBDC0, then issues one 8-byte BULK
  OUT to EP15 and observes the bus for 200 us.
- Verdict: `caliptra_ss_usb_handshake_counter_callback` counts device-sourced
  ACK/NAK/STALL packets inside that window. The count must be 0.
- The VIP transfer-level device-response timeout is expected and is demoted to
  UVM_INFO by an inline `uvm_report_catcher`; it is deliberately not the
  verdict, because a timeout is also what a broken testbench looks like.
- There is no positive control phase: the ACKed control transfers of the
  preceding enumeration already prove the link and the counting path are alive.
- Firmware is minimal. An unsupported endpoint has no descriptor slot to
  program or watch, so the MCU only services enumeration.

## Run

```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_unsupported_ep_test
```

# File contains AI-generated response based on internal company sources
