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
// Description: MCU firmware for caliptra_ss_usb_hs_dev_err_iso_token_mismatch.
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype bin packet_unexpected (0x3) - the
// same bin caliptra_ss_usb_hs_dev_err_pkt_unexpected and
// caliptra_ss_usb_hs_dev_err_iso_stalled already close. This test's value is
// RTL line/branch coverage of usb_pie.m.vhdl lines 2192/2211/2231/2251 - see
// the matching sequence's header for the full rationale.
//
// WHY THIS SUITE DOES NOT USE usb_err_inject_fw_common.h
//
// Same reason as caliptra_ss_usb_hs_dev_err_iso_pid_seq: the firmware's only
// job is to arm EP2 OUT/IN as isochronous ONCE and then get out of the way.
// The actual stimulus is driven entirely by
// caliptra_ss_usb_hs_dev_err_iso_token_mismatch_sequence on the packet
// sequencer - see that file's header for why the VIP transfer layer cannot
// express "send this token before the DUT's pending ISO state has cleared."
//
// WHY BOTH EP2 OUT AND EP2 IN ARE HIGH-BANDWIDTH (2-TRANSACTION) ENDPOINTS
//
// Reading usb_pie.m.vhdl's USB_PROT_WF_TOKEN_BYTE3 case statement shows the
// four target PACKET_UNEXPECTED branches (lines 2192/2211/2231/2251) are
// keyed ONLY on iso_out_pending_r/iso_in_pending_r, independent of which
// endpoint the stray token addresses. iso_out_pending_r/iso_in_pending_r are
// set on the FIRST OUT/IN of an isochronous transfer and cleared again as
// soon as the LAST transaction of that transfer completes
// (iso_transact_cnt_down reaches "00"). For a single-transaction transfer
// (NBYTES bits [11:10]="00"), that happens on the very first data phase, so
// by the time the FSM returns to USB_PROT_WF_TOKEN_BYTE3 waiting for a new
// token, the pending flag has ALREADY cleared and the mismatched token can
// never land in the "unexpected" window - this was the root cause of the
// original (now-superseded) design's failure to hit any of the four lines.
//
// The fix is to configure BOTH EP2 OUT and EP2 IN as 2-transaction
// high-bandwidth (HBW) isochronous endpoints (NBYTES bits [11:10]="01",
// USB_EP2_NBYTES_HBW below). iso_transact_cnt_down then loads to "01" on
// the first transaction and only DECREMENTS (to "00") when that first
// transaction completes - iso_out_pending_r/iso_in_pending_r stay asserted
// throughout, exactly the window the sequence's mismatched token needs.
// The sequence completes only the first transaction (legal MDATA for OUT,
// ordinary data for IN - see its header for the required PID framing) and
// then substitutes a mismatched token for what would have been the second
// transaction's token.
//
// WHY EP2 IN CAN BE ARMED UP FRONT NOW
//
// The superseded design deferred arming EP2 IN until after the third EP2
// OUT completion, reasoning (incorrectly) that an already-armed EP2 IN
// would make the DUT answer a bare directed IN token as an ordinary ISO IN
// request instead of taking the "unexpected" branch. That reasoning
// conflated two unrelated bugs: the PID_IN branch's decision depends only
// on iso_out_pending_r (see above), not on EP2 IN's arm state. With the
// pending flags now correctly held across the token boundary by the HBW
// transaction count, EP2 IN can be armed alongside EP2 OUT on the very
// first control transfer with no interaction between the two endpoints.
//
// WHY THE FIRMWARE SEES EXACTLY ONE EP2OUT/EP2IN COMPLETION PER LEG, THEN
// NONE FROM THE MISMATCHED TOKENS
//
// Each leg's first (legitimate) data phase completes normally through the
// DMA and raises DEV0_CSR_INTSTAT_EP2OUT or EP2IN once; the firmware re-arms
// the endpoint after each such completion so the next leg starts fresh. The
// mismatched token that follows is discarded by one of the four target RTL
// branches before any DMA handoff, so it raises no further completion -
// confirmed by usb_pie.m.vhdl: all four branches route straight to
// USB_PROT_WF_IDLE via set_pie_error/clear_pie_success without touching the
// DMA interface.

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

// EP2 OUT buffer and list offset. Same addresses as
// caliptra_ss_usb_hs_dev_err_pkt_unexpected.c / err_iso_pid_seq.c so the ISO
// tests in this family agree on the SRAM map.
#define USB_SRAM_EP2_OUT_BUF_OFFSET    0x600u
#define USB_EP_LIST_EP2_OUT_OFFSET     0x020u

// EP2 IN buffer and list offset, needed for the line-2211 leg
// (iso_in_pending_r = '1'). Single descriptor only (see header note on why
// two separate buffer entries is wrong for this purpose) - SRAM placed well
// after the OUT buffer so the two never overlap.
#define USB_SRAM_EP2_IN_BUF_OFFSET     0xA00u
#define USB_EP_LIST_EP2_IN_BUF0_OFFSET 0x028u

// NBYTES value placing iso_transact_cnt_down in the "01" (2-transaction)
// high-bandwidth bucket on load (usb_dma.m.vhdl load_iso_transact_cnt_down
// reads epinfo_nbytes(11 downto 10)). 1536 = 0x600 has bits [11:10] = "01".
// Used for BOTH EP2 OUT and EP2 IN - see the file header for why both
// endpoints must be HBW for the pending flags to survive the first
// transaction. Each endpoint uses a single descriptor sized to this value;
// the first (and only, in this test) transaction's actual on-wire payload
// is capped at 1024 bytes by packetsize_decod's "first transactions" branch
// (usb_pie.m.vhdl ~line 858/866), with the remaining bytes never sent since
// the sequence never completes a second transaction.
#define USB_EP2_NBYTES_HBW             1536u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Arm EP2 OUT as a 2-transaction high-bandwidth isochronous endpoint: T=1
// (periodic) with the RF bit clear (ISO selector), NBYTES in the "01"
// bucket. Re-armed after every completion so each leg's first data phase
// lands on a freshly armed endpoint.
static void usb_ep2_out_arm_iso_hbw(void) {
    uint32_t inten;
    uint32_t ep2_out = USB_EP_ENTRY_ACTIVE
                     | USB_EP_ENTRY_TYPE_PERIODIC
                     | USB_EP_ENTRY_RF_ISO
                     | USB_EP_ENTRY_NBYTES(USB_EP2_NBYTES_HBW)
                     | USB_EP_ENTRY_ABS_ADDR(USB_DMA_BASE_ADDR
                                             + USB_SRAM_EP2_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP2_OUT_OFFSET, ep2_out);

    inten = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTEN);
    lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTEN,
                 inten | DEV0_CSR_INTSTAT_EP2OUT_MASK);
    VPRINTF(LOW, "MCU: EP2 OUT (ISO, HBW 2-transaction) armed for %d bytes\n",
            USB_EP2_NBYTES_HBW);
}

// Arm EP2 IN as a 2-transaction high-bandwidth isochronous endpoint,
// needed for the line-2211 leg (iso_in_pending_r = '1' at the moment a
// mismatching PID_OUT token arrives). Single descriptor, NBYTES in the
// same "01" bucket as EP2 OUT - see the file header for why.
static void usb_ep2_in_arm_iso_hbw(void) {
    uint32_t inten;

    for (uint32_t i = 0; i < USB_EP2_NBYTES_HBW; i += 4) {
        uint32_t w = 0x11223344u + i;
        lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP2_IN_BUF_OFFSET + i, w);
    }

    uint32_t ep2_in_buf0 = USB_EP_ENTRY_ACTIVE
                         | USB_EP_ENTRY_TYPE_PERIODIC
                         | USB_EP_ENTRY_NBYTES(USB_EP2_NBYTES_HBW)
                         | USB_EP_ENTRY_ABS_ADDR(USB_DMA_BASE_ADDR
                                                  + USB_SRAM_EP2_IN_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP2_IN_BUF0_OFFSET, ep2_in_buf0);

    inten = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTEN);
    lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTEN,
                 inten | DEV0_CSR_INTSTAT_EP2IN_MASK);
    VPRINTF(LOW, "MCU: EP2 IN (ISO, HBW 2-transaction) armed for %d bytes\n",
            USB_EP2_NBYTES_HBW);
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
    uint32_t ep2out_completions = 0;
    uint32_t ep2in_completions = 0;
    bool     ep2_out_armed      = false;
    bool     ep2_in_armed       = false;
    bool     host_stop_seen     = false;

    VPRINTF(LOW, "=================\nMCU: USB error injection - ISO token-direction mismatch (HBW)\n=================\n\n");

    boot_mcu();
    boot_usb_core_hub();
    usb_hub_connect();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    // There is no local completion event to stop on for the mismatched
    // tokens themselves - they are discarded by the RTL before any
    // DMA/interrupt is raised. The host releases the MCU when its checks
    // are done.
    for (poll_count = 0;
         poll_count < USB_POLL_TIMEOUT && !host_stop_seen;
         poll_count++) {

        usb_handle_bus_reset();
        reg_data = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT);

        if (reg_data & DEV0_CSR_INTSTAT_DEV_INT_MASK) {
            uint32_t cmd = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
            if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
                if (ep2_out_armed) {
                    // A bus reset wipes the descriptor, so the arm has to be
                    // redone once enumeration restarts.
                    ep2_out_armed = false;
                    VPRINTF(LOW, "MCU: Bus reset - EP2 OUT arm cleared\n");
                }
                if (ep2_in_armed) {
                    ep2_in_armed = false;
                    VPRINTF(LOW, "MCU: Bus reset - EP2 IN arm cleared\n");
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
                // Both EP2 OUT and EP2 IN are armed up front - see the file
                // header's "WHY EP2 IN CAN BE ARMED UP FRONT NOW" note.
                if (!ep2_out_armed) {
                    usb_ep2_out_arm_iso_hbw();
                    ep2_out_armed = true;
                }
                if (!ep2_in_armed) {
                    usb_ep2_in_arm_iso_hbw();
                    ep2_in_armed = true;
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

        // Each leg's first (legitimate) OUT data phase completes normally.
        // Re-arm EP2 OUT so the next leg starts with a fresh buffer.
        if (reg_data & DEV0_CSR_INTSTAT_EP2OUT_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP2OUT_MASK);
            ep2out_completions++;
            usb_ep2_out_arm_iso_hbw();
        }

        // Each leg's first (legitimate) IN data phase completes normally.
        // Re-arm EP2 IN so the next leg starts with a fresh buffer.
        if (reg_data & DEV0_CSR_INTSTAT_EP2IN_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP2IN_MASK);
            ep2in_completions++;
            usb_ep2_in_arm_iso_hbw();
        }

        if (poll_count % 10000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x EP2OUT=0x%x\n",
                    poll_count,
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT),
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT),
                    lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP2_OUT_OFFSET));
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

    VPRINTF(LOW, "MCU: ISO token-direction mismatch: %d control transfers, %d EP2 OUT completions, %d EP2 IN completions\n",
            transfers_handled, ep2out_completions, ep2in_completions);

    VPRINTF(LOW, "MCU: USB error injection - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
