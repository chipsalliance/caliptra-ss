# caliptra_ss_usb_hs_dev_err_stall

Makes USBDC0 EP1 return a STALL handshake to a High-Speed bulk OUT.

## Coverage target

`usb_transfer_outcome_cg.cp_errortype` bin **`sent_stall` (0xA)** of
`src/usb/coverage/usb_dev_ep_cov.sv`, assigned at `usb_pie.m.vhdl` lines 2391, 2528 and 2816.

The bin was at zero before this test existed, because nothing in the
regression ever produced a protocol error on a device endpoint.

## Mechanism

**No injection at all.** The firmware arms EP1 OUT with STALL set and ACTIVE
clear, which is literally the RTL guard
`epinfo_stall = '1' and epinfo_active = '0'`; `usb_dma.m.vhdl` latches both
bits straight out of the descriptor the firmware writes
(`dma_rdata(29)` / `dma_rdata(31)`, i.e. `USB_EP_ENTRY_STALL` /
`USB_EP_ENTRY_ACTIVE`). The sequence only supplies an ordinary,
uncorrupted bulk OUT for the device to stall.

**Why the existing hub STALL test does not cover this.**
`caliptra_ss_usb_hs_hub_class_req_stall` stalls control requests against the
**hub** at address 1. The PIE is time-multiplexed across hub/dev0/dev1, and
`usb_cov_probe_caliptra_ss.sv` instantiates `usb_dev_ep_cov` for dev0 and
dev1 only - there is no hub instance - so a hub STALL is never sampled by this
coverpoint.

The endpoint is left halted when the test ends, on purpose: a functional stall
persists until the host clears it (USB 2.0 section 8.4.5), so unlike the
corruption tests this one has no recovery leg.

## Run

```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_stall_test
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
