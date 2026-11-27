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
//
// Description: MCU firmware for caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw.
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype bin pid_unknown (0x2), RTL site
// usb_pie.m.vhdl line 2704 (USB_PROT_OUT_SETUP_WF_RX_DATA_PID, PID_DATA0
// branch, "iso_mdata_cnt_up /= 00" case). This is a FORKED sibling of
// caliptra_ss_usb_hs_dev_err_iso_pid_seq, not an edit to it - see that
// test's README "LINE 2704 IS NOT CLOSED BY THIS SUITE" note for why: line
// 2704 requires iso_mdata_cnt_up to be nonzero, which requires a prior
// ACCEPTED MDATA packet, which requires a high-bandwidth (HBW) endpoint -
// the opposite endpoint configuration from the single-buffer, non-HBW
// endpoint that suite deliberately uses to close lines 2632/2655/2680.
// Forking avoids any risk of the HBW endpoint config regressing that
// suite's already-closed coverage.
//
// WHY THIS SUITE DOES NOT USE usb_err_inject_fw_common.h
//
// Same reason as caliptra_ss_usb_hs_dev_err_iso_pid_seq: the firmware's only
// job is to arm EP2 OUT as a high-bandwidth isochronous endpoint and then
// get out of the way. The actual stimulus (a directed OUT token, then a
// legitimate first MDATA data phase to arm iso_mdata_cnt_up, then a second
// directed OUT token followed by a mismatching DATA0 data packet) is driven
// entirely by caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw_sequence on the
// packet sequencer - see that file's header for why the VIP transfer layer
// cannot express either of these two packets.
//
// WHY THE FIRMWARE SEES ONE EP2OUT COMPLETION, THEN NONE
//
// The sequence's first MDATA data phase (sent as the first of 3 possible
// HBW transactions on this endpoint, the "10" iso_transact_cnt_down bucket -
// see USB_EP2_OUT_NBYTES below) IS accepted by the RTL as ordinary ISO OUT
// data: usb_pie.m.vhdl's PID_MDATA branch (line 2632) only reports
// pid_unknown when "iso_transact_cnt_down = 00 or iso_mdata_cnt_up = 10";
// neither is true on the first packet of this endpoint, so the MDATA is
// accepted, iso_mdata_cnt_up increments to "01" (incr_iso_mdata_cnt_up,
// usb_pie.m.vhdl ~line 2645), and the RTL reaches its normal DMA handoff -
// this firmware sees exactly one DEV0_CSR_INTSTAT_EP2OUT completion for it
// and re-arms the endpoint for the second transaction. The sequence's
// SECOND data phase sends PID_DATA0 instead of the expected MDATA/DATA1;
// line 2704's guard ("iso_mdata_cnt_up /= 00") is now true, so the RTL
// reports pid_unknown and returns the FSM to WF_IDLE without reaching a DMA
// step - no further EP2OUT completion is expected after that.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Fallback poll ceiling only. The normal exit is the host STOP handshake
// below; this bound is what applies when the host never sends one.
#define USB_POLL_TIMEOUT               60000u

// EP2 OUT buffer and list offset. Same addresses as the non-HBW sibling
// suite (caliptra_ss_usb_hs_dev_err_iso_pid_seq.c) - these are two separate
// standalone test binaries, so there is no SRAM-map conflict between them.
#define USB_SRAM_EP2_OUT_BUF_OFFSET    0x600u
#define USB_EP_LIST_EP2_OUT_OFFSET     0x020u

// NBYTES for the EP2 OUT descriptor, chosen to put iso_transact_cnt_down
// into a HIGH-BANDWIDTH bucket on load (usb_dma.m.vhdl
// load_iso_transact_cnt_down reads epinfo_nbytes(11 downto 10)). 2048 has
// bits [11:10] = "10", the three-transaction HBW bucket (USB 2.0 section
// 5.9.2: a HBW ISO OUT endpoint carries MDATA, MDATA, DATA2 across up to 3
// packets per microframe). This is the opposite of the non-HBW sibling
// suite's deliberately-chosen 1023-byte ("00" bucket) endpoint.
#define USB_EP2_OUT_NBYTES             2048u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Arm EP2 OUT as a high-bandwidth isochronous endpoint: T=1 (periodic) with
// the RF bit clear (ISO selector), NBYTES in the HBW bucket. Re-armed after
// the first (legitimate) data phase completes, so the sequence's second
// data phase - the mismatching DATA0 - lands on a freshly armed endpoint
// with iso_mdata_cnt_up still carrying the value the first phase set.
static void usb_ep2_out_arm_iso_hbw(void) {
    uint32_t inten;
    uint32_t ep2_out = USB_EP_ENTRY_ACTIVE
                     | USB_EP_ENTRY_TYPE_PERIODIC
                     | USB_EP_ENTRY_RF_ISO
                     | USB_EP_ENTRY_NBYTES(USB_EP2_OUT_NBYTES)
                     | USB_EP_ENTRY_ABS_ADDR(USB_DMA_BASE_ADDR
                                             + USB_SRAM_EP2_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP2_OUT_OFFSET, ep2_out);

    inten = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTEN);
    lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTEN,
                 inten | DEV0_CSR_INTSTAT_EP2OUT_MASK);
    VPRINTF(LOW, "MCU: EP2 OUT (ISO, high-bandwidth) armed for %d bytes\n",
            USB_EP2_OUT_NBYTES);
}

static uint32_t usb_ep2_out_read(void) {
    return lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP2_OUT_OFFSET);
}

// Has the host told us it is finished with the device?
//
// Reuses the MCI generic-wire command channel from the OCP-recovery work -
// see caliptra_ss_usb_hs_dev_err_pkt_unexpected.c for the full note.
static bool usb_err_host_stop_seen(void) {
    uint32_t command = lsu_read_32(SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_1);

    if ((command >> USB_LEGACY_EP0_COMMAND_MAGIC_SHIFT) !=
            USB_LEGACY_EP0_COMMAND_MAGIC)
        return false;
    if (((command >> USB_LEGACY_EP0_COMMAND_OPCODE_SHIFT) &
            USB_LEGACY_EP0_COMMAND_NIBBLE_MASK) != USB_LEGACY_EP0_COMMAND_STOP)
        return false;

    lsu_write_32(SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1,
        ((uint32_t)USB_LEGACY_EP0_COMMAND_ACK_MAGIC <<
         USB_LEGACY_EP0_COMMAND_MAGIC_SHIFT) | (command & 0x00FFFFFFu));
    return true;
}

void main(void) {
    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t transfers_handled = 0;
    uint32_t ep2_completions   = 0;
    bool     ep2_armed         = false;
    bool     host_stop_seen    = false;

    VPRINTF(LOW, "=================\nMCU: USB negative testing - ISO out-of-sequence DATA0 (HBW)\n=================\n\n");

    boot_mcu();
    boot_usb_core_hub();
    usb_hub_connect();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    // One EP2 OUT completion is expected (the first, legitimate MDATA data
    // phase). The second data phase (mismatching DATA0) is discarded by the
    // RTL before any DMA/interrupt is raised. The host releases the MCU
    // when its checks are done.
    for (poll_count = 0;
         poll_count < USB_POLL_TIMEOUT && !host_stop_seen;
         poll_count++) {

        usb_handle_bus_reset();
        reg_data = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT);

        if (reg_data & DEV0_CSR_INTSTAT_DEV_INT_MASK) {
            uint32_t cmd = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
            if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
                if (ep2_armed) {
                    // A bus reset wipes the descriptor, so the arm has to be
                    // redone once enumeration restarts.
                    ep2_armed = false;
                    VPRINTF(LOW, "MCU: Bus reset - EP2 arm cleared\n");
                }
            }
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_DEV_INT_MASK);
        }

        if (reg_data & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0OUT_MASK);
            uint32_t cmd = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
            if (cmd & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();
                transfers_handled++;
                if (!ep2_armed) {
                    usb_ep2_out_arm_iso_hbw();
                    ep2_armed = true;
                }
            } else {
                // Status-stage ZLP OUT of a control read completed; re-arm
                // EP0 OUT or enumeration stalls.
                usb_ep0_arm_out();
            }
        }

        if (reg_data & DEV0_CSR_INTSTAT_EP0IN_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);
        }

        // EP2 OUT completion is EXPECTED exactly once here (the first,
        // legitimate MDATA data phase). Re-arm so the sequence's second
        // data phase (the mismatching DATA0) has a fresh buffer - that
        // phase itself must NOT raise a second completion, since that
        // would mean the DATA0 was accepted as ordinary data rather than
        // hitting line 2704.
        if (reg_data & DEV0_CSR_INTSTAT_EP2OUT_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP2OUT_MASK);
            ep2_completions++;
            VPRINTF(LOW,
                "MCU: EP2 OUT (ISO) completion %d - entry 0x%x.%s\n",
                ep2_completions, usb_ep2_out_read(),
                (ep2_completions == 1)
                    ? " Expected: the first MDATA phase."
                    : " UNEXPECTED beyond the first: the DATA0 packet was accepted as ordinary data and the pid_unknown bin likely did not close at line 2704.");
            usb_ep2_out_arm_iso_hbw();
        }

        if (poll_count % 10000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x EP2=0x%x\n",
                    poll_count,
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT),
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT),
                    usb_ep2_out_read());
        }

        // Checked last so the current iteration still serviced EP0 before the
        // loop exits.
        host_stop_seen = usb_err_host_stop_seen();
    }

    if (host_stop_seen)
        VPRINTF(LOW, "MCU: host STOP received after %d poll iterations; halting\n",
                poll_count);
    else
        VPRINTF(LOW, "MCU: no host STOP within %d poll iterations; halting anyway\n",
                poll_count);

    VPRINTF(LOW, "MCU: ISO out-of-sequence DATA0 (HBW): %d control transfers, %d EP2 OUT completions\n",
            transfers_handled, ep2_completions);

    VPRINTF(LOW, "MCU: USB negative testing - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
