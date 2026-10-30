// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Description: USB HS device L1 (LPM Sleep) entry firmware with a
// DEVICE-INITIATED L1 exit. This is the device-driven counterpart of
// caliptra_ss_usb_hs_dev_lpm_l1: the stimulus, the UVM test class and the
// classification logic are identical, and the only difference is who ends the
// L1 dwell. Here the host deliberately stays quiet and this firmware rings the
// LPM remote-wakeup doorbell itself.
//
// The split into two suites is forced by the build model, not by preference:
// the exit leg is selected by USB_LPM_DEVICE_INITIATED_EXIT, which is a
// compile-time define, and MCU firmware cannot read UVM plusargs. One image
// cannot serve both legs, so each leg gets its own suite and the two must be
// kept in agreement:
//   caliptra_ss_usb_hs_dev_lpm_l1            host-driven, no BUILD_CFLAGS,
//                                            no +usb_lpm_dev_wakeup
//   caliptra_ss_usb_hs_dev_lpm_l1_dev_wakeup this suite,
//                                            -DUSB_LPM_DEVICE_INITIATED_EXIT=1
//                                            and +usb_lpm_dev_wakeup=1
// Mismatching them is silent: plusarg without the define means nobody drives
// the exit and the DUT sits in L1 to the sequence dwell ceiling; the define
// without the plusarg means host and device both drive a resume and the log
// cannot attribute which one woke the link.
//
// L1 differs structurally from L2 (global suspend): entry is an explicit
// packet on the wire (EXT token + LPM token carrying bLinkState=1, HIRD and
// bRemoteWake), not the absence of SOFs. So this test does NOT use the
// sof_off trick of caliptra_ss_usb_hs_dev_global_suspend_L2; the host-side
// UVM sequence sends svt_usb_protocol_service_usb_20_lpm_sequence instead.
//
// What this firmware does:
//   1. Standard hub + HS device bring-up and EP0 enumeration service.
//   2. Confirms DEVCMDSTAT.LPM_SUP reads 1 (LPM enabled out of reset in
//      ip_xxx_3511 usb_reg_if.m.vhdl, reg_dev_lpm_sup <= '1').
//   3. Watches DEVCMDSTAT.DSUS_C - which this IP shares between L2 and L1
//      state changes - and on each event records DEVCMDSTAT.LPM_SUS,
//      DEVCMDSTAT.LPM_REWP and LPM[3:0] HIRD_HW.
//   4. Exits when both the L1 entry and the L1 exit have been seen.
//
// HOW THE DEVICE-INITIATED EXIT ACTUALLY REACHES THE BUS. DEVCMDSTAT.LPM_SUS
// is read-only status, not a control bit: in usb_reg_if.m.vhdl
// reg_dev_lpm_suspend <= sync_lpm_suspend and it is only ever presented on the
// read path (reg_rdata(19)). Firmware therefore cannot clear it. What the
// write in usb_request_lpm_remote_wakeup() does is ring a doorbell encoded in
// that read-only bit POSITION:
//
//   if reg_wdata(19) = '0' and reg_dev_lpm_suspend = '1'
//                          and reg_dev_lpm_remote_wake = '1' then
//     usbreg_lpmremotewakeup <= '1';
//
// usbreg_lpmremotewakeup is a separate flop. It self-clears later, once
// reg_dev_lpm_suspend goes back to 0. On the dev0 instance (usb_reg_if_1) that
// flop is wired straight to hub_port_lpmremotewakeup(0), which fans out two
// ways in ip_xxx_3511_hs_mem_compound_structure.a.vhdl:
//   - hub bookkeeping: usb_app_hw_hub.m.vhdl clears hub_port_l1_int(0) and
//     raises hub_port_l1_change(0), i.e. the C_PORT_L1 status bit.
//   - upstream resume: the hub_lpmremotewakeup OR-tree feeds the top-level
//     usbreg_lpmremotewakeup, and usb_pie.m.vhdl leaves
//     BUS_EVENT_LPM_SUSPEND_L1 on it ("DEVICE asserts its own RESUME"),
//     driving K for T_60us before rejoining the normal wakeup path.
//
// So no connect/disconnect of a downstream device is needed to wake the hub:
// the OR-tree already admits each enumerated port's own wakeup request. The
// causal order is doorbell -> hub -> K upstream -> link leaves L1 -> LPM_SUS
// reads 0, which is the reverse of what the bit name suggests.
//
// Both preconditions the doorbell needs are already satisfied by the shared
// sequence: entering L1 gives dev0_lpm_suspend (LPM_SUS=1) because
// hub_port_enable(0) is set, and the sequence hardcodes LPM_BREMOTEWAKE=1,
// which arrives as dev0_lpm_rw and reads back as LPM_REWP=1.
//
// DIRECT-TOKEN PATH, DEV0 ONLY. The LPM token this firmware observes is
// addressed to DEV0. DEV1 has no software-visible LPM control of its own, so
// there is no DEV1 variant of this firmware.
//
// That is not a gap in L1 coverage. Since release_2.6 the hub implements
// SetAndTestPortFeature(PORT_L1), and in
// ip_xxx_3511_hs_mem_compound_structure.a.vhdl the per-port LPM inputs are
// taken from each device (hub_port_lpm_sup(0) <= dev0_lpm_sup,
// hub_port_lpm_sup(1) <= dev1_lpm_sup) while hub_port_l1(N) drives
// devN_lpm_suspend. Both ports are therefore reachable through the hub, which
// is what caliptra_ss_usb_dual_device_hs_hub_port_l1 covers.
//
// Note for whoever reuses this classification code in the hub-level test
// (caliptra_ss_usb_dual_device_hs_hub_port_l1, the only other L1 test - the
// hub request SetAndTestPortFeature(PORT_L1) is legal only against a
// downstream port, so there is no separate hub-targeted L1 test):
// because hub_port_l1(N) is ORed into devN_lpm_suspend, a hub-driven PORT_L1
// shows up here identically to a direct LPM token - same DEVCMDSTAT.LPM_SUS,
// same shared DSUS_C. The logic below needs no change for that path.
// See docs/usb_l1_lpm_test_feasibility_report.md.

//
// Hub-composite IP: USBDC0 is an embedded downstream device of the on-chip
// 2-port hub, so its registers live at USB_DEV_* (base 0x20001000) and the
// hub must be connected upstream by firmware before the host sees anything.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Ceiling on the DEVCMDSTAT polling loop, not a dwell. The loop exits as soon
// as both L1 change events have been observed.
#define USB_POLL_TIMEOUT 50000

// One DSUS_C event on L1 entry, one on L1 exit.
#define USB_LPM_EVENTS_EXPECTED 2

// NO IN-L1 DWELL. This firmware rings the remote-wakeup doorbell as soon as it
// sees LPM_SUS, and that is deliberate.
//
// An earlier version of this test padded the time spent in L1 with register
// reads and MCU console writes so that clk_off_counter (CLOCKOFF_CYCLE = 255
// pie_clk ticks, 4.25 us at 60 MHz of continuous clock_on = 0) could reach 0
// and let utmi_suspendm fall. That was done purely to satisfy the SuspendM
// edge checker, which this suite no longer runs - see the yml for why that
// coverage belongs to the host-driven twin and to the L2 suites instead.
//
// Keeping the dwell was not neutral, it was harmful. The L1 window the host
// grants is shorter than the padded dwell, so L1 closed before the doorbell
// was written and the write was silently dropped: the readback came back with
// LPM_SUS = 0, meaning usbreg_lpmremotewakeup was never set and the device K
// that CHK_DEVICE_WAKEUP_K is there to observe was never driven by the
// doorbell. The write must land while reg_dev_lpm_suspend is still 1, so the
// correct behaviour is to issue it immediately.
//
// Do not reintroduce a dwell here to chase a SuspendM edge. On the
// device-initiated leg the two goals are in direct conflict - time spent
// waiting for the PHY to power down is time taken away from the window in
// which the doorbell can still be accepted.


// Set to 1 to build the device-initiated L1 exit variant (firmware asserts
// usbreg_lpmremotewakeup instead of waiting for the host to resume). The UVM
// sequence must then be run without its host-driven clear leg, which is what
// +usb_lpm_dev_wakeup=1 selects.
// This suite exists to exercise the device-driven leg, so the default here is
// 1 - the opposite of caliptra_ss_usb_hs_dev_lpm_l1. The yml still passes
// -DUSB_LPM_DEVICE_INITIATED_EXIT=1 explicitly so the intent is visible in the
// run recipe and so the two suites cannot be told apart only by which
// directory they live in.
#ifndef USB_LPM_DEVICE_INITIATED_EXIT
#define USB_LPM_DEVICE_INITIATED_EXIT 1
#endif


volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main(void) {
    uint32_t reg_data;
    uint32_t lpm_reg;
    uint32_t poll_count;
    uint32_t intstat;
    uint32_t lpm_events = 0;
    uint32_t l1_entry_seen = 0;
    uint32_t l1_exit_seen  = 0;
    uint32_t hird_hw_at_entry = 0xFFFFFFFFu;
    uint32_t rewp_at_entry = 0;

    VPRINTF(LOW, "MCU: hs_dev_lpm_l1_dev_wakeup test (device-initiated L1 exit)\n");
    boot_mcu();

    // Brings up USBDC0 in HS mode and, on the hub-composite IP, sets HUB_EN.
    boot_usb_core_hub();

    // Two-phase hub bring-up: HUB_EN inside boot_usb_core_hub(), HUB_CONNECT here
    // once USBDC0's EP list / DEVCMDSTAT / DCON are fully programmed. Only
    // after this does the host see the hub, chirp HS, and enumerate USBDC0.
    usb_hub_connect();

    mcu_cptra_advance_brkpoint();

    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    // Release the unconditional UTMI clock request so the controller can
    // actually drop its clock in a low-power link state. Same rationale as
    // the L2 test: FORCE_NEEDCLK holds usbreg_pll_on, which holds clock_on,
    // which keeps reloading clk_off_counter, which pins utmi_suspendm high.
    usb_allow_clock_stop();

    // LPM capability check. reg_dev_lpm_sup defaults to '1' at reset, so a 0
    // here means either the wrong base address or that something cleared it
    // during bring-up - both fatal to the rest of the test.
    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    if (reg_data & DEV0_CSR_DEVCMDSTAT_LPM_SUP_MASK) {
        VPRINTF(LOW, "MCU: LPM_SUP set, controller accepts LPM tokens (DEVCMDSTAT=0x%x)\n",
                reg_data);
    } else {
        VPRINTF(LOW, "MCU: ERROR LPM_SUP clear, controller will STALL LPM tokens (DEVCMDSTAT=0x%x)\n",
                reg_data);
    }

    // Log the LPM register out of reset. HIRD_HW must be 0 before any LPM
    // token has arrived; it is the reference for the post-entry comparison.
    lpm_reg = lsu_read_32(USB_DEV_LPM);
    VPRINTF(LOW, "MCU: LPM reg at start = 0x%x (HIRD_HW=%d DATA_PENDING=%d)\n",
            lpm_reg,
            (int)(lpm_reg & DEV0_CSR_LPM_HIRD_HW_MASK),
            (int)((lpm_reg & DEV0_CSR_LPM_DATA_PENDING_MASK) ? 1 : 0));

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {
        usb_handle_bus_reset();
        reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
        intstat  = lsu_read_32(USB_DEV_INTSTAT);
        if (intstat & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0OUT_MASK);
            if (reg_data & DEV0_CSR_DEVCMDSTAT_SETUP_MASK)
                usb_handle_control_transfer();
        }
        if (intstat & DEV0_CSR_INTSTAT_EP0IN_MASK)
            lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);

        if (reg_data & DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK) {
            // DSUS_C is shared between the L2 and L1 state changes in this IP
            // (usb_reg_if.m.vhdl asserts it when either sync_suspend or
            // sync_lpm_suspend changes), so classify the event from the live
            // state bits rather than assuming which one moved.
            lpm_reg = lsu_read_32(USB_DEV_LPM);
            lpm_events++;

            if (reg_data & DEV0_CSR_DEVCMDSTAT_LPM_SUS_MASK) {
                l1_entry_seen = 1;
                rewp_at_entry = (reg_data & DEV0_CSR_DEVCMDSTAT_LPM_REWP_MASK) ? 1u : 0u;
                hird_hw_at_entry = lpm_reg & DEV0_CSR_LPM_HIRD_HW_MASK;
                VPRINTF(LOW, "MCU: L1 ENTRY event %d DEVCMDSTAT=0x%x LPM=0x%x HIRD_HW=%d REWP=%d\n",
                        lpm_events, reg_data, lpm_reg,
                        (int)hird_hw_at_entry, (int)rewp_at_entry);
            } else if (reg_data & DEV0_CSR_DEVCMDSTAT_DSUS_MASK) {
                // L2, not L1. Not the stimulus this test is for, but worth
                // logging: it usually means SOFs stopped instead of an LPM
                // token being sent.
                VPRINTF(LOW, "MCU: L2 suspend event %d (not L1) DEVCMDSTAT=0x%x\n",
                        lpm_events, reg_data);
            } else if (l1_entry_seen) {
                l1_exit_seen = 1;
                VPRINTF(LOW, "MCU: L1 EXIT event %d DEVCMDSTAT=0x%x LPM=0x%x\n",
                        lpm_events, reg_data, lpm_reg);
            } else {
                VPRINTF(LOW, "MCU: suspend-change event %d with no low-power state set DEVCMDSTAT=0x%x\n",
                        lpm_events, reg_data);
            }

#if (USB_LPM_DEVICE_INITIATED_EXIT == 1)
            // Device-initiated exit. Do this BEFORE acknowledging DSUS_C:
            // usb_request_lpm_remote_wakeup() performs the write that both
            // drives LPM_SUS to 0 (the actual wakeup command) and sets
            // DSUS_C, so a separate acknowledge here would be redundant and
            // would also risk clearing the event this branch is reacting to.
            if (l1_entry_seen && !l1_exit_seen) {
                // Ring the doorbell immediately, with nothing between the
                // DSUS_C event that reported L1 entry and this write.
                //
                // The write is only latched if reg_dev_lpm_suspend is still 1
                // when it reaches usb_reg_if.m.vhdl:
                //
                //   if reg_wdata(19) = '0' and reg_dev_lpm_suspend = '1'
                //                          and reg_dev_lpm_remote_wake = '1'
                //
                // There is no retry and no error - a write that arrives after
                // L1 has already closed is simply ignored, so the only visible
                // symptom is that no device K ever appears. Any delay inserted
                // here is therefore spent out of the budget for that window.
                // See the note at the top of this file for why the padding
                // that used to sit here was removed.
                if (usb_request_lpm_remote_wakeup())
                    VPRINTF(LOW, "MCU: device-initiated L1 exit driven\n");
                continue;
            }

#endif
            // DSUS_C is write-1-to-clear. Read-modify-write the LIVE value so
            // no status bit that changed in the meantime is clobbered.
            lsu_write_32(USB_DEV_DEVCMDSTAT,
                lsu_read_32(USB_DEV_DEVCMDSTAT) | DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK);

            // Both halves of the L1 cycle observed: stop polling. The
            // run_phase objection in caliptra_ss_usb_base_test is only
            // released once this function halts the MCU, so spinning on to
            // the ceiling would hold the whole simulation open for no extra
            // coverage. The UVM sequence owns its own objection and its own
            // observation window, so host-side checking is unaffected.
            if (l1_entry_seen && l1_exit_seen) {
                VPRINTF(LOW, "MCU: L1 entry and exit both observed after %d polls\n",
                        poll_count + 1);
                break;
            }
            if (lpm_events >= (USB_LPM_EVENTS_EXPECTED + 2u)) {
                VPRINTF(LOW, "MCU: %d suspend-change events without a clean L1 cycle; giving up\n",
                        lpm_events);
                break;
            }
        }
    }

    if (!l1_entry_seen)
        VPRINTF(LOW, "MCU: ERROR no L1 entry observed (LPM_SUS never set) after %d polls\n",
                poll_count);
    else if (!l1_exit_seen)
        VPRINTF(LOW, "MCU: ERROR L1 entered but never exited (LPM_SUS stuck) after %d polls\n",
                poll_count);
    else
        VPRINTF(LOW, "MCU: L1 cycle complete, HIRD_HW seen at entry = %d, REWP = %d\n",
                (int)hird_hw_at_entry, (int)rewp_at_entry);

    VPRINTF(LOW, "MCU: hs_dev_lpm_l1_dev_wakeup test complete\n");

    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
