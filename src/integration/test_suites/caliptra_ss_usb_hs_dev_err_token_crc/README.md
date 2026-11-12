# caliptra_ss_usb_hs_dev_err_token_crc

Corrupts the CRC5 of the token packet of a High-Speed bulk OUT to USBDC0 EP1.

## Coverage target

`usb_transfer_outcome_cg.cp_errortype` bin **`token_crc` (0x4)** of
`src/usb/coverage/usb_dev_ep_cov.sv`, assigned at `usb_pie.m.vhdl`, two assignment sites.

The bin was at zero before this test existed, because nothing in the
regression ever produced a protocol error on a device endpoint.

## Mechanism

Same sequence as the data-CRC test, with `crc_target` set to
`CRC5_ERROR` instead. CRC5 covers the token's address and endpoint fields
rather than the data payload, so the device rejects the transaction before any
data phase.

One sequence class serves both CRC bins; the test sets the selector on the
instance in `build_phase`.

## Run

```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_token_crc_test
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
