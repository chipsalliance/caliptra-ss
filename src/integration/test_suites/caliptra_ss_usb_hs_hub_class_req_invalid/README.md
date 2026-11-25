# caliptra_ss_usb_hs_hub_class_req_invalid

Hub **class-request INVALID** test (High Speed, hub only). It extends
`caliptra_ss_usb_hs_hub_class_req_stall`: parent steps 1-9 run unchanged
through `super.body()`, then steps 10-24 are added. Suffix / message ID:
`USB_HUB_CLASS_REQ_INVALID`.

The target is code + toggle coverage of
`third_party/usb2/src/usb_hub_composite_device/RTL/RTL/usb_app_hw_hub.m.vhdl`
(the copy the regression compiles - merged-coverage page `mod16.html`).

## Line targets

The requested line list uses the parent README's numbering, which is **9
lines behind** the current file. Mapping, with the merged-coverage status from
`latest_merged_cov` (2026-11-18):

| Requested | Current | Code | Before | Stimulus |
|---|---|---|---|---|
| 103 | 112 | ClearPortFeature bad port, stall | covered | parent 3 |
| 125 | 134 | ClearPortFeature bad wValue, stall | covered | parent 4 |
| **128** | **137** | ClearHubFeature `null` | **0/1** | step 10 |
| 133 | 142 | GetPortStatus bad port, stall | covered | parent 7 |
| 138 | 147 | SetPortFeature bad port, stall | covered | parent 5 |
| 158 | 167 | SetPortFeature bad wValue, stall | covered | parent 6 |
| **161** | **170** | SetHubFeature `null` | **0/1** | step 11 |
| 214 | 223 | ClearPortFeature bad port `null` | covered | parent 3 |
| **228** | **237** | ClearPortFeature accepted no-op | **0/1** | step 12 |
| 248 | 257 | ClearPortFeature `when others` | covered | parent 4 |
| 259 | 268 | SetPortFeature bad port `null` | covered | parent 5 |
| **275** | **284** | SetPortFeature accepted no-op | **0/1** | step 13 |
| 286 | 295 | SetPortFeature `when others` | covered | parent 6 |

Current line **286** (`SetPortFeature(PORT_ENABLE)`) was also 0/1 and is step
14; step 15 clears it again.

## Toggle targets

Missing bins on `usb_app_hw_hub` input ports before this test:

| Port | Missing |
|---|---|
| `EP0_WVALUE` | [7:5], [12], [15:14] both edges; [10] 1->0 |
| `EP0_WINDEX` | [3:2], [6:5], [8] both edges; [7] 1->0 |
| `EP0_REQUEST` | [5:4] both edges |

* `ep0_wvalue` / `ep0_windex` are the raw SETUP bytes
  (`usb_ep0_handler.m.vhdl:292-293`), so they toggle even on a rejected
  request. Step 20 sends wValue `0xD4E0`, step 21 wIndex `0x01EC` (both must
  STALL); every later leg drives those bits back to 0.
* `ep0_request` is **not** the host bRequest: it is the opcode stored in the
  matched hub SETUP-table row (`usb_ep0_handler.m.vhdl:192`), cleared to 0 when
  nothing matches (lines 207/241). No shipped row sets bits 5:4, so undefined
  class bRequest codes (step 22) are stalled by the EP0 handler and cannot
  toggle them. The firmware therefore patches the GetHubStatus row opcode (hub
  table word 157, `0x2000_1274`) `0xFFFF4042 -> 0xFFFF4072` before
  `boot_usb_core_hub()`. Step 23 GetHubStatus then presents opcode `0x72`,
  which lands in `when others => null` and must COMPLETE. Step 24 brings the
  opcode back to `0x42`.

## Steps added

| # | Request | wValue | wIndex | Expected |
|---|---|---|---|---|
| 10 | ClearHubFeature (0x20/0x01) | 0 | 0 | complete |
| 11 | SetHubFeature (0x20/0x03) | 0 | 0 | complete |
| 12 | ClearPortFeature | PORT_POWER 8 | 1 | complete |
| 13 | SetPortFeature | PORT_POWER 8 | 1 | complete |
| 14 | SetPortFeature | PORT_ENABLE 1 | 1 | complete |
| 15 | ClearPortFeature | PORT_ENABLE 1 | 1 | complete (restore) |
| 16 | ClearPortFeature | C_PORT_CONNECTION 16 | 4 | STALL (table mask) |
| 17 | SetPortFeature | PORT_RESET 4 | 255 | STALL (table mask), no reset |
| 18 | SetAndTestPortFeature | PORT_L1 10 | 3 | STALL (line 175) |
| 19 | SetAndTestPortFeature | 5 | 1 | STALL (line 176) |
| 20 | ClearPortFeature | 0xD4E0 | 1 | STALL (wValue toggle) |
| 21 | GetPortStatus | 0 | 0x01EC | STALL (wIndex toggle) |
| 22 | class bRequest 0x02/04/05/08/09/0B/FF out, 0x0A in | 0 | 1 | STALL each |
| 23 | GetHubStatus (patched row, opcode 0x72) | 0 | 0 | complete |
| 24 | GetPortStatus | 0 | 1 | complete (control leg) |

Port numbers 4..255 on Clear/Set/GetPortStatus never reach `usb_app_hw_hub`:
the SETUP-table rows compare wIndex with mask `0xFFFC`, so only port 3 is
stalled by the hub decoder (parent steps) and 4..255 are stalled earlier by the
EP0 handler. SetAndTestPortFeature has a `0x0000` wIndex mask, so its port-3
leg (step 18) does reach the hub decoder.

## Files

| File | Note |
|---|---|
| `caliptra_ss_usb_hs_hub_class_req_invalid.c` | parent bring-up + EP0 poll loop + GetHubStatus opcode patch (layout and read-back checks, FAIL-only verdict) |
| `caliptra_ss_usb_hs_hub_class_req_invalid.yml` | `+UVM_TESTNAME=caliptra_ss_usb_hs_hub_class_req_invalid_test` |
| `cptra_bringup.c` | symlink to `../libs/usb/bringup/cptra_bringup.c` |
| `.../uvm/usb/caliptra_ss_usb_hs_hub_class_req_invalid_sequence.svh` | extends the class_req_stall sequence |
| `.../uvm/usb/caliptra_ss_usb_hs_hub_class_req_invalid_test.svh` | HS only |

## Status

**Code and docs only - not compiled or simulated.** First-run checks:

```
grep 'hub SETUP table patch' mcu_console.log    # mask_lsb(after)=0xffff4072
grep '^UVM_ERROR' vcs_sim.log                   # must be EMPTY
grep -E '=== STEP|USB_HUB_CLASS_REQ_INVALID' svt_debug.transcript
```

Then confirm in the run's coverage report that current lines 137/170/237/284/286
are hit and the toggle bins above are covered.

Risks to look at first if it fails:

* Step 23 reported STALLED: check the patch read-back line before suspecting
  the DUT.
* Steps 10/11 STALLED: the ClearHubFeature / SetHubFeature rows have wValue
  mask `0xFFFE`, so only wValue 0/1 is admitted; the test uses 0.
* The step 23 payload is `hub_status(data_index)` for the last latched
  `data_index`. GetHubStatus with opcode `0x72` latches nothing, so it is
  whatever the previous legal-port leg left (expected port 1, latched by step
  19). Reported only, never asserted.
* Step 14 drives `hub_port_enable[0]` high for the short window until step 15.
  The host never addresses USBDC0 (address 2) in this test, so nothing else
  can observe it.

<!-- File contains AI-generated response based on internal company sources -->
