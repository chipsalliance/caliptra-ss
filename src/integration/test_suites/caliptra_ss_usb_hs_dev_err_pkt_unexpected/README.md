# caliptra_ss_usb_hs_dev_err_pkt_unexpected

Sends a well-formed isochronous OUT to a USBDC0 endpoint that is no longer armed, at High Speed.

## Coverage target

`usb_transfer_outcome_cg.cp_errortype` bin **`packet_unexpected` (0x3)** of
`src/usb/coverage/usb_dev_ep_cov.sv`, assigned at `usb_pie.m.vhdl` line 2879.

The bin was at zero before this test existed, because nothing in the
regression ever produced a protocol error on a device endpoint.

## Mechanism

**No injection at all, and isochronous rather than bulk.** The firmware arms
ISO EP2 OUT exactly once and then refuses to re-arm it; the sequence sends two
ISO OUT transfers. Hardware clears ACTIVE when it consumes the first, so the
second arrives at an endpoint with ACTIVE low - the RTL branch
`epinfo_active = '0' and crc16_valid_nxt = '1'` on an iso endpoint. Both
packets are perfectly formed and the CRC16 is valid; the branch even requires
it.

**Why this test is isochronous.** All seven live assignment sites of 0x3 are
gated on an outstanding isochronous transaction. The gating flags
`iso_in_pending_r` / `iso_out_pending_r` are set only under
`if epinfo_iso = '1'` (line 2500), and `epinfo_iso` comes from the endpoint
type bits of the list entry. On a bulk endpoint both flags stay low and all
five token-mismatch branches are dead, so a bulk sequencing error cannot reach
this bin.

Line 2879 was chosen over the other six sites because it is the only one
deterministic from the host side alone: the token-mismatch branches race the
SOF boundary and the DMA handler, and line 2837 additionally needs the
endpoint STALLed, which the `sent_stall` test already covers.

## Run

```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_pkt_unexpected_test
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
