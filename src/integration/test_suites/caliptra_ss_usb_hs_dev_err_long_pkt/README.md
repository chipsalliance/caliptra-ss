# caliptra_ss_usb_hs_dev_err_long_pkt

Elongates a High-Speed bulk OUT data packet to USBDC0 EP1 past wMaxPacketSize.

## Coverage target

`usb_transfer_outcome_cg.cp_errortype` bin **`overrun` (0xB)** of
`src/usb/coverage/usb_dev_ep_cov.sv`, assigned at `usb_pie.m.vhdl`, two assignment sites.

The bin was at zero before this test existed, because nothing in the
regression ever produced a protocol error on a device endpoint.

## Mechanism

Host-side `svt_usb_packet_exception` with
`error_kind == LENGTH_ERROR` and `length_error == LONG_PACKET_ERROR`. The
injected transfer is deliberately sized at exactly one max packet so the
elongation crosses the wMaxPacketSize boundary, which is what the overrun path
keys on.

The firmware EP1 buffer is 1024 bytes rather than 512 so an elongated packet
has somewhere to land.

## Run

```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_long_pkt_test
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
