# caliptra_ss_usb_hs_hub_ep0_unsupported_features_valid_port

High-Speed, hub-only, Directed. A **code-coverage** test for the compound hub
EP0 request decoder `usb_ep0_handler.m.vhdl`.

Host misbehaviour scenario: every request is legal on the wire but either asks
for a feature the hub does not support or carries a SETUP field pattern the hub
SETUP-match table does not admit, so the required behaviour is an EP0 STALL or
a clamped data stage.

- UVM test: `caliptra_ss_usb_hs_hub_ep0_unsupported_features_valid_port_test`
- Sequence: `caliptra_ss_usb_hs_hub_ep0_unsupported_features_valid_port_sequence`
- Enumeration: `hub_enum_stepA` only (hub at address 1, downstream ports left
  un-powered, USBDC0 never enumerated)
- Transfers: EP0 control only. No data endpoint is touched.

## Steps and the RTL lines they target

| # | Request | Expected | `usb_ep0_handler.m.vhdl` |
|---|---------|----------|--------------------------|
| 1 | `GET_CONFIGURATION` wLength=1 | COMPLETE, data `0x01` | 359-361 |
| 2 | `GET_CONFIGURATION` wLength=2 | COMPLETE, 1 byte | 218-220 wLength clamp |
| 3 | `GET_STATUS(INTERFACE)` | COMPLETE, `0x0000` | 371-372 |
| 4 | `GET_STATUS(DEVICE)` wLength=4 | COMPLETE, 2 bytes | 218-220 again |
| 5 | `SET_FEATURE(DEVICE)` wValue=`0x0003` | **STALL** | 339-341 `ep0_in_stall` |
| 6 | `GET_STATUS(ENDPOINT)` wIndex=`0x0082` | **STALL** | 244-246 then 205-207 |
| 7 | `SYNCH_FRAME` (bRequest `0x0C`) | **STALL** | 205-207 |
| 8 | `SetAndTestHubPortFeature` wIndex=`0x0001` | **STALL** | 239-241 |
| 9 | `GET_CONFIGURATION` wLength=1 | COMPLETE | recovery proof |

FSM arcs covered: `READ_SETUP_MASK_LSB -> SETUP_DONE` (steps 6, 7) and
`READ_SETUP_MASK_MSB -> READ_SETUP_LSB` (step 6). Step 8 additionally covers
`READ_SETUP_MASK_MSB -> SETUP_DONE`.

Step 4 runs BEFORE step 5 on purpose: the stalled `SET_FEATURE` of step 5 still
latches `set_remote_wake_enabled` (line 334-337, because wValue bit 0 is set),
which is bit 1 of the device status word step 4 checks.

## The firmware SETUP-table patch

The last row of the hub SETUP-match table is `SetAndTestHubPortFeature`
(`usb_ep0_hub_descr.m.vhdl:421-425`) and its `SETUP_MASK_MSB` is `X"00000000"`,
i.e. wIndex is entirely don't-care. The STALL leg at lines 239-241 needs a
last-row wIndex MISMATCH, which is therefore arithmetically impossible with the
reset table.

The table is not a ROM at run time: `C_EP0_ROM` is only the reset value of the
writable array `ep0_mem` (`:72`, `:476`), and any word below `C_NWORDS = 196`
is writable from the hub aperture while `hub_write_lock` is 0 (`:495-502`).
`hub_write_lock` is `HUB_EN and HUB_DCON` (`:528`).

So `caliptra_ss_usb_hs_hub_ep0_unsupported_features_valid_port.c` writes hub table word 195
(absolute `0x2000_130C`, inside the `0x2000_1040`..`0x2000_130F` aperture) from
`0x00000000` to `0x0000FFFF` BEFORE `boot_usb_core_hub()`, with a layout sanity
check on word 192 (`0x00000CA3`) and a read-back check. Both checks increment
`total_errors` and the firmware verdict is FAIL-only.

Containment: `SetAndTestHubPortFeature` (bmRequestType `0xA3`, bRequest `0x0C`)
is issued by no other test, and the patch is a run-time register write done
only by this test's firmware, so no other test is affected.

## Documented coverage waivers

- **line 165** (`device <= device + 1`) is structurally dead:
  `usb_ep_config_hub_pkg.p.vhdl:26` sets `C_NBDEV = 1`, so the guard at line
  162 is a tautology.
- **line 477** (`PROC_EP0_MEM_ACCESS` `SETUP_DECODE -> USB_DATA` on a grant with
  a pending `upd_dma_req`) is an internal arbiter race that cannot be driven
  directly. The long table walks of steps 6-8 maximise the chance of hitting
  it; the test does not assert it.

Full write-up including the FS word indices:
`docs/usb/usb_ep0_handler_coverage_map.md` in the accessories repo.

## Notes

- The `.c` file's IDE errors (`cannot open source file "soc_ifc.h"`) are
  include-path artefacts present in every USB test `.c` and must NOT be fixed.
- No `uvm_report_catcher` and no `device_timeout` relaxation are needed: every
  stalled transfer is terminated by a real STALL handshake, which the VIP
  reports as `svt_sequence_item::ABORTED`, so nothing ever hits a device
  response timeout.
- An FS sibling is possible but adds no new RTL lines (every decode path above
  is speed independent). Its last SETUP row would be words 152..155
  (`SETUP_MASK_MSB` at `0x2000_126C`), since the FS table has no
  DEVICE_QUALIFIER / OTHER_SPEED_CONFIGURATION rows.

<!-- File contains AI-generated response based on internal company sources -->
