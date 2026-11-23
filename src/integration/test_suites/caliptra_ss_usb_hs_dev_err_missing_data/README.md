# caliptra_ss_usb_hs_dev_err_missing_data

Part of the `caliptra_ss_usb_hs_dev_err_*` family. See
`caliptra-ss/docs/CaliptraSSUSBErrorInjection.md` for the shared mechanism
and why every sequence ends with the MCU STOP handshake.

- Target: `usb_transfer_outcome_cg.cp_errortype` bin `timeout` (0x6).
- RTL site: `usb_pie.m.vhdl` line 2442 ("TIMEOUT: Data Packet or epinfo_valid
  is not received on time" after an OUT/SETUP token is accepted for an armed
  endpoint).
- Mechanism: a lone, well-formed OUT token is sent to USBDC0 EP1 with NO
  exception attached and deliberately no following DATA packet
  (`caliptra_ss_usb_err_inject_packet_sequence` with `attach_exception=0`).
  This is not a wire corruption; the fault is purely "nothing follows the
  token". The sequence then waits 100us (well beyond the RTL's internal
  `MAX_PACKET_HANDLING_TIMER`, `PACKET_EVENT_TIMEOUT_HS = 127`) before
  issuing the recovery transfer.
- Status: expected PASS - the PIE must report TIMEOUT for the lone token and
  the endpoint must recover on the clean transfer that follows.
