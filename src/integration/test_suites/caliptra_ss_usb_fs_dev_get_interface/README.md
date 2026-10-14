# caliptra_ss_usb_fs_dev_get_interface

Full-Speed variant of `caliptra_ss_usb_hs_dev_get_interface`: standard USB 2.0
**GET_INTERFACE** (section 9.4.4) issued to the compound hub and to USBDC0,
with both responses checked host-side by `caliptra_ss_usb_data_check_api`.

## Scope

| Item | Value |
|------|-------|
| Link speed | Full Speed (VIP `high_speed_capable = 0`, firmware `boot_usb_core_fs()` sets `DEVCMDSTAT.PFSC`) |
| Targets | hub @ address 1, USBDC0 @ address 2 (hub downstream port 1) |
| Request | `bmRequestType = 0x81`, `bRequest = 0x0A`, `wValue = 0`, `wIndex = 0`, `wLength = 1` |
| Expected data | one byte, `bAlternateSetting = 0x00`, for both targets |

## Composition

- UVM test: `caliptra_ss_usb_fs_dev_get_interface_test`
  (`testbench/uvm/usb/caliptra_ss_usb_fs_dev_get_interface_test.svh`)
- Host sequence: `caliptra_ss_usb_get_interface_sequence` - shared verbatim with
  the HS variant. The test only applies the FS VIP conversion block
  (FS-only mode, FS endpoint re-stamp, widened FS link timing), exactly like
  `caliptra_ss_usb_fs_dev_get_status_test`.
- Firmware: `caliptra_ss_usb_fs_dev_get_interface.c` - pure polling EP0 loop
  (no ISR, no `mcu_isr.h`), with `USB_POLL_TIMEOUT = 8000`.

## Answer sources

- The hub answers GET_INTERFACE entirely in EP0 hardware (SETUP-match ROM entry
  `0x00000A81`, constant data byte `0x00`).
- USBDC0 answers from the shared EP0 dispatcher
  `usb_handle_control_transfer()` in `test_suites/libs/usb/usb.c`, which keeps a
  per-controller `usb_alt_setting` shadow (cleared on bus reset) and STALLs if
  the device is not Configured or `wIndex != 0`.

No test-specific firmware logic and no hub descriptor/SETUP-table change are
required.

## Verdict

Host-side only: the verdict comes from UVM/VIP `UVM_ERROR` / `UVM_FATAL`
counted in `caliptra_ss_usb_base_test::final_phase`. The firmware never emits
`TB_CMD_TEST_PASS`; no `.mk` file and no extra plusarg are needed.

## Run

```
+UVM_TESTNAME=caliptra_ss_usb_fs_dev_get_interface_test
```

See also `docs/handover/claude_md/18_usb_get_interface_test.md` in the NXP DV
accessories repo.
