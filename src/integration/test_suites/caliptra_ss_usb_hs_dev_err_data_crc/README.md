# caliptra_ss_usb_hs_dev_err_data_crc

Corrupts the CRC16 of a High-Speed bulk OUT data packet to USBDC0 EP1.

## Coverage target

`usb_transfer_outcome_cg.cp_errortype` bin **`data_crc` (0x5)** of
`src/usb/coverage/usb_dev_ep_cov.sv`, assigned at `usb_pie.m.vhdl` line 2953 - the only assignment site of this code in the
whole PIE.

The bin was at zero before this test existed, because nothing in the
regression ever produced a protocol error on a device endpoint.

## Mechanism

Host-side `svt_usb_packet_exception` with `error_kind == CRC_ERROR` and
`crc_error == CRC16_ERROR`, attached to the middle of three bulk OUT
transfers by `caliptra_ss_usb_hs_dev_err_crc_sequence`. A single-bit
`mask_or_value` is used because the mask is XORed with the CRC field, so 0
would leave it correct.

The device returns **no handshake at all** for a bad data CRC (the RTL comment
at the assignment site says so explicitly), so the host sees the transfer
abort or time out. That is correct per USB 2.0 section 8.7.1. The clean
transfer that follows is the real check: it proves the endpoint recovered.

## Run

```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_data_crc_test
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
