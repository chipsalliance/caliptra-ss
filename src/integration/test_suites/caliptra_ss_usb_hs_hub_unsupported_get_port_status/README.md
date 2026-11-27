# caliptra_ss_usb_hs_hub_unsupported_get_port_status

GetPortStatus (and friends) on an **unsupported port** of the embedded USB hub.
High Speed, hub only, Directed. Suffix / MSG_ID
`HUB_UNSUPPORTED_GET_PORT_STATUS`.

A code / branch coverage test for the hub class decoder
`usb_app_hw_hub.m.vhdl`, written as a host-misbehaviour scenario: fourteen EP0
control transfers to the hub at address 1, five of which must be STALLed. No
data endpoint is touched and no device controller is enumerated.

| | |
|---|---|
| Speed | High Speed |
| Topology | hub only (`hub_enum_stepA`), hub at address 1, downstream ports never powered |
| Transfers | EP0 control only |
| UVM test | `caliptra_ss_usb_hs_hub_unsupported_get_port_status_test` |
| Sequence | `caliptra_ss_usb_hs_hub_unsupported_get_port_status_sequence` |
| Firmware | plain hub bring-up + EP0 poll loop, no SETUP-table patch, no verdict byte |

---

## 1. Which RTL this targets, and which copy

`third_party/usb2/src/usb_hub_composite_device/RTL/RTL/usb_app_hw_hub.m.vhdl`
(469 lines). That is the copy the regression compiles - see
`src/integration/config/usb_hub_upstream.vhdl.vf`, which is the default
`USB_HUB_VHDL_FILELIST` in `tools/scripts/Makefile`. Two other copies of this
file exist in the workarea with different line numbering; do not use them to
read the line references below.

**Line numbers in a coverage request are often in the OLD usb2 numbering,
9 lines behind this file.** The four arms originally requested for this test
map as follows:

| requested | current | process | arm |
|---|---|---|---|
| 128 | **137** | `PROC_CLASS_STALL` | `else --ClearHubFeature  null` |
| 161 | **170** | `PROC_CLASS_STALL` | `else --SetHubFeature    null` |
| 214 | **223** | `PROC_REQUEST_HANDLING` | ClearPortFeature bad port `null` |
| 228 | **237** | `PROC_REQUEST_HANDLING` | ClearPortFeature accepted no-op |

Always map requested numbers against the merged coverage report before writing
stimulus for this file.

## 2. Two filters sit between the host and the hub decoder

1. **The hub SETUP-match table.** `usb_ep0_hub_descr.m.vhdl:362-365` gives the
   `GetHubPortStatus` row a wIndex mask of `0xFFFC`. Port **3** passes the mask
   and is stalled by the hub decoder at line 142. Ports **4..255** do not match
   the row at all: the walk falls off the table and `usb_ep0_handler` stalls
   them at `205-207` / `239-241`, so they add no `usb_app_hw_hub` coverage.
   Steps 1-3 exercise both layers on purpose so the log says which one fired.
2. **`ep0_request` is not the host `bRequest`.** It is the 7-bit opcode of the
   matched table row (`usb_ep0_handler.m.vhdl:192`), cleared to 0 when nothing
   matches. An undefined class `bRequest` therefore never reaches this decoder.
   That is why this test drives only shipped request rows and does no
   `EP0_REQUEST` toggle work - that belongs to
   `caliptra_ss_usb_hs_hub_class_req_invalid`, which patches a row opcode from
   firmware in order to do it.

## 3. Step list

| # | Request | Expected | RTL target |
|---|---|---|---|
| 1 | `GetPortStatus` wIndex=3 | **STALL** | 141-142, plus the 264 MISSING_ELSE |
| 2 | `GetPortStatus` wIndex=4 | **STALL** | SETUP mask `0xFFFC`, `usb_ep0_handler` |
| 3 | `GetPortStatus` wIndex=`0x01FF` | **STALL** | same, upper wIndex byte |
| 4 | `GetHubStatus` wIndex=0 | COMPLETE, 4 bytes | 262-263, `data_index <= 0` |
| 5 | `ClearHubFeature` wValue 0 wIndex 0 | COMPLETE no-op | **136-137** |
| 6 | `SetHubFeature` wValue 0 wIndex 0 | COMPLETE no-op | **169-170** |
| 7 | `ClearPortFeature(PORT_POWER)` port 1 | COMPLETE no-op | **227-237** |
| 8 | `ClearPortFeature(C_PORT_CONNECTION)` port 3 | **STALL** | **222-223** + 111-112 |
| 9 | `SetPortFeature(PORT_ENABLE)` port 1 | COMPLETE | 285-286, arms 11-12 |
| 10 | `ClearPortFeature(PORT_L1)` port 1 | COMPLETE | **branch hole, 243-247** |
| 11 | `SetAndTestPortFeature(PORT_L1)` port 1 | COMPLETE, **1 byte** | **branch hole, 305-315** |
| 12 | `SetAndTestPortFeature` wValue 5 port 1 | **STALL** | 174-177 |
| 13 | `ClearPortFeature(PORT_ENABLE)` port 1 | COMPLETE | restores step 9 |
| 14 | `GetPortStatus` port 1 | COMPLETE, 4 bytes | recovery proof |

`wValue` must be **0** on steps 5 and 6: the `ClearHubFeature` /
`SetHubFeature` rows carry a wValue mask of `0xFFFE`, so only 0 and 1 match the
row at all, and 0 (`C_HUB_LOCAL_POWER`) is what a real host sends.

### The ROM wLength cap is PER ROW - do not share a length constant

Steps 11 and 12 request **1** byte (`L1_STATUS_LEN`), not 4. The
`SetAndTestHubPortFeature` row caps wLength at 1
(`usb_ep0_hub_descr.m.vhdl:423`, word A+2 = `0x00010000`) because USB 2.0
section 11.24.2.13 defines its data stage as a single port-L1 status byte;
`GetHubStatus` and `GetPortStatus` cap at 4 (`:357`, `:363`).

Asking for 4 on the cap-1 row **does not stall** - the clamp at
`usb_ep0_handler.m.vhdl:218-220` silently shortens the reply to 1 byte - so a
checker expecting 4 reports a DUT failure on a leg that actually worked. The
first revision of this test failed exactly that way. `report_status_word()`
therefore takes an explicit `expected_bytes` argument instead of hardcoding 4.

## 4. The two branch holes, and why the step order is load bearing

**Hole 1 - `ClearPortFeature(PORT_L1)` with `hub_port_l1_int` already 0**
(lines 243-247). The inner `if hub_port_l1_int(var_port) = '1'` guard had only
ever been taken TRUE, by the L1 tests which clear a port that really is in L1.
Step 10 clears L1 on a port that was never put into L1, so the guard goes
FALSE and the L1 change bit must not be set.

**Hole 2 - `SetAndTestPortFeature(PORT_L1)` with the LPM condition FALSE**
(lines 305-315). The outer condition needs the port ENABLED; the inner LPM
condition is the hole. Measured reachability: `hub_lpm_sup(i)` is driven from
`dev0_lpm_sup` / `dev1_lpm_sup` (structure lines 2329 / 2331) and
`hub_port_lpm_hird_sw` from `dev0_lpm_hird_sw` / `dev1_lpm_hird_sw`
(2371 / 2379). **This is a hub-only test, so neither device controller is
enumerated and `dev*_lpm_sup` is 0**, which makes the inner condition FALSE and
takes exactly the uncovered leg.

So: step 9 provides the enable, steps 10-12 take the legs, step 13 takes the
enable away. **Do not reorder steps 9-13.** Leaving the ports unpowered is also
deliberate, for the same reason.

## 5. Rig: STALL, not silence - so no report catcher

Every rejected request here ends in a **real STALL handshake**, which the VIP
reports cleanly as `svt_sequence_item::ABORTED`. Nothing times out, so unlike
the unsupported-endpoint and disabled-endpoint families this test needs **no
`uvm_report_catcher` and no `device_timeout` relaxation**, and `UVM_ERROR` must
be exactly **0** on a passing run. Use that as the discriminator when choosing
the rig for a new negative test: *silence* needs the catcher rig, *STALL* needs
only `check_setup_stalled()`.

## 6. State safety

Step 9 is the only leg that changes decoder state and step 13 undoes it. No
`PORT_RESET` is ever issued on a legal port, so no bus reset is injected into
USBDC0, and the host only ever talks to address 1, so the device controller is
never addressed. Step 14 is a legal `GetPortStatus` that must COMPLETE, so a
DUT that wedges EP0 after the first stall cannot pass.

## 7. Firmware

A plain hub bring-up (`boot_usb_core_hub()`, then `usb_hub_connect()` after
Caliptra bring-up) plus the standard EP0 poll loop, identical in shape to
`caliptra_ss_usb_hs_hub_class_req_stall`. `USB_POLL_TIMEOUT` is 5000, which is
far more than fourteen EP0 control transfers with no data phase longer than
four bytes need.

There is **no firmware verdict byte** and **no SETUP-table patch**. The
accept/reject decision is taken entirely in hardware - `PROC_CLASS_STALL` is
combinational on `ep0_request` / `ep0_windex` / `ep0_wvalue` and
`PROC_REQUEST_HANDLING` is clocked off the same fields - so the firmware
observes nothing it could assert on, and every leg goes through a request row
exactly as shipped. If a future revision ever does need a table patch, it must
run BEFORE `boot_usb_core_hub()`, because `hub_write_lock` is
`HUB_EN and HUB_DCON`.

## 8. Not covered here (waivers)

| line | why no stimulus exists |
|---|---|
| 357 | needs a DEVICE-initiated remote wakeup from a SUSPENDED, enabled port - that is the remote-wakeup rig, not an EP0 decode test |
| 365 | same, for the L1 / LPM remote wakeup path |
| 456, 460 | the `C_DATAWIDTH = 32` leg and the unsupported-width `assert false`. `C_DATAWIDTH` is 64 in this configuration, so both are structurally dead |

## 9. How to run

```
python3 ./caliptra_ss_nxp_dv_accessories/tools/run_caliptra_test.py \
    -test caliptra_ss_usb_hs_hub_unsupported_get_port_status
```

It is also registered in the nightly list, in the command-value-check list and
in the focused coverage-fill list
`src/integration/stimulus/USB_COV_FILL_caliptra_ss_top_tb_regression.yml`
(accessories repo), whose header carries the `-coverage` run command and the
matching single-run coverage merge.

First-run checks:

```
grep '^UVM_ERROR' vcs_sim.log                            # must be EMPTY (section 5)
grep 'HUB_UNSUPPORTED_GET_PORT_STATUS' vcs_sim.log        # 14 outcome lines, 5 stalled=1
grep 'BRANCH HOLE' vcs_sim.log                            # steps 10 and 11 must COMPLETE
grep 'returned 1 status byte' vcs_sim.log                 # step 11, the cap-1 row
```

Then check the coverage report for lines 137 / 170 / 223 / 237 and for the two
branch rows `CLEAR_FEATURE / 10 / 0` and `SET_AND_TEST / ... / 0`.

If step 11 reports a STALL rather than completing, check that the ports really
were left unpowered - a sibling change that enumerates a device controller
would raise `dev*_lpm_sup` and silently move the branch back to its covered
leg.

<!-- File contains AI-generated response based on internal company sources -->
