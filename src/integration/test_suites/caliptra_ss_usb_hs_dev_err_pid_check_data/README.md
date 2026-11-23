# caliptra_ss_usb_hs_dev_err_pid_check_data

Part of the `caliptra_ss_usb_hs_dev_err_*` family. See
`caliptra-ss/docs/CaliptraSSUSBErrorInjection.md` for the shared mechanism,
VIP field model, and why every sequence ends with the MCU STOP handshake.

- Target: `usb_transfer_outcome_cg.cp_errortype` bin `pid_encoding` (0x1).
- RTL site: `usb_pie.m.vhdl` line 2777 (bad PID check in the DATA PID of an
  OUT/SETUP data phase).
- Mechanism: `PID_CHECK_ERROR` injected on a DATA0 packet of a bulk OUT to
  USBDC0 EP1, preceded by a clean directed OUT token (so the PIE is in its
  data phase when the corrupted DATA0 arrives). Differs from
  `caliptra_ss_usb_hs_dev_err_pid_check`, which corrupts the TOKEN's PID
  (line 2130), a different live site of the same errortype code.
- Status: expected PASS - the device must reject the corrupted DATA0 and the
  endpoint must recover on the clean transfer that follows.
