# caliptra_ss_usb_hs_dev_err_pid_illegal

Sends a DATA packet whose PID is not a legal data PID, on USBDC0 EP1 at High Speed.

## Coverage target

`usb_transfer_outcome_cg.cp_errortype` bin **`pid_unknown` (0x2)** of
`src/usb/coverage/usb_dev_ep_cov.sv`, assigned at `usb_pie.m.vhdl`, nine assignment sites - the most widely reached error code
in the design.

The bin was at zero before this test existed, because nothing in the
regression ever produced a protocol error on a device endpoint.

## Mechanism

Host-side `svt_usb_packet_exception` with
`error_kind == ILLEGAL_DATA_PID_ERROR`, also a standalone `error_kind`.
Unlike the PID-check test the byte is self-consistent - it simply decodes to a
PID the device does not accept in that position.



## Run

```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_pid_illegal_test
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
