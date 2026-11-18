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
// job is to arm EP2 OUT as isochronous ONCE and then get out of the way. The
// actual stimulus (ISO OUT data phases interleaved with directed mismatched
// tokens on the packet sequencer) is driven entirely by
// caliptra_ss_usb_hs_dev_err_iso_token_mismatch_sequence - see that file's
// header for why the VIP transfer layer cannot express "send this token
// before the DUT's pending ISO state has cleared."
//
// WHY THE FIRMWARE NEVER SEES AN EP2OUT COMPLETION FROM THE MISMATCHED TOKENS
//
// All four usb_pie.m.vhdl branches this test targets (lines 2192/2211/2231/
// 2251) clear iso_out_pending_r/iso_in_pending_r and return the protocol FSM
// straight to USB_PROT_WF_IDLE without ever reaching the DMA handoff that
// would raise DEV0_CSR_INTSTAT_EP2OUT or EP2IN. The sequence's own ISO OUT
// data phases (used only to arm iso_out_pending_r before each mismatch) DO
// complete normally, so this firmware re-arms EP2 OUT each time it sees a
// completion, exactly as caliptra_ss_usb_hs_dev_iso_out_sequence's firmware
// would, just without an ISO IN response path since no real ISO IN transfer
// is ever requested.
//
// WHY EP2 IN IS ARMED AFTER THE THIRD EP2 OUT COMPLETION, NOT ON THE FIRST
// CONTROL TRANSFER
//
// A regression run proved arming EP2 IN immediately (alongside EP2 OUT, on
// the first SETUP transfer) is a bug: the sequence's very first leg sends a
// directed, unanswered PID_IN token to EP2 meant to hit line 2192 (PID_IN
// while iso_out_pending_r='1'). With EP2 IN already ACTIVE at that point,
// the DUT does not take the "unexpected" branch at all - it treats the bare
// IN token as an ordinary isochronous IN request and answers it with a real
// 768-byte DATA0 packet (confirmed in svt_debug.transcript: a report_xact
// entry for DATA0, Payload Size=768, lands exactly at the moment
// [register_fail:...rx_packet_routed_check] fires). The VIP never registered
// a transfer-level request for that bare IN token, so it has no routing
// entry to match the DUT's unsolicited response against, and the check
// fails with "No device with matching address found."
//
// The sequence's body() issues exactly three do_iso_out() arming transfers
// (for the 2192/2231/2251 legs) before reaching the final leg, which pairs
// a directed IN (to arm iso_in_pending_r) with a directed OUT (to hit line
// 2211). EP2 IN must stay inactive until that final leg, so it is armed
// only after the third EP2 OUT completion - one poll loop iteration after
// the third do_iso_out() finishes - instead of on the first control
// transfer.

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

// EP2 IN buffer and list offsets, needed for the line-2211 leg
// (iso_in_pending_r = '1'). Same convention as
// caliptra_ss_usb_hs_dev_err_pkt_unexpected.c: two buffer entries at
// 0x028/0x02C, SRAM placed after the OUT buffer so the two never overlap.
#define USB_SRAM_EP2_IN_BUF_OFFSET     0xA00u
#define USB_EP_LIST_EP2_IN_BUF0_OFFSET 0x028u
#define USB_EP_LIST_EP2_IN_BUF1_OFFSET 0x02Cu

// HS isochronous max packet (USB 2.0 table 5-7).
#define USB_ISO_TRANSFER_BYTES         1024u

// NBYTES for the EP2 IN descriptor. iso_transact_cnt_down loads from
// epinfo_nbytes(11 downto 10) (usb_dma.m.vhdl load_iso_transact_cnt_down).
// 1536 has bits [11:10] = "01", so the first IN data packet only
// decrements iso_transact_cnt_down (usb_pie.m.vhdl USB_PROT_IN_TX_CRC16_BYTE2,
// "else decr_iso_transact_cnt_down") instead of clearing iso_in_pending_r
// (the "elsif iso_transact_cnt_down = 00 then clear_iso_in_pending" leg) -
// this is what lets iso_in_pending_r survive to the end of the microframe so
// the sequence's directed PID_OUT token (line 2211) lands while it is still
// set. Each of the two buffer entries carries half (768 bytes).
#define USB_EP2_IN_NBYTES_TOTAL        1536u
#define USB_EP2_IN_BUF_BYTES           (USB_EP2_IN_NBYTES_TOTAL / 2u)


volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Arm EP2 OUT as isochronous: T=1 (periodic) with the RF bit clear (ISO
// selector). Re-armed after every normal completion so each of the
// sequence's three OUT data phases lands on a freshly armed endpoint.
static void usb_ep2_out_arm_iso(void) {
    uint32_t inten;
    uint32_t ep2_out = USB_EP_ENTRY_ACTIVE
                     | USB_EP_ENTRY_TYPE_PERIODIC
                     | USB_EP_ENTRY_RF_ISO
                     | USB_EP_ENTRY_NBYTES(USB_ISO_TRANSFER_BYTES)
                     | USB_EP_ENTRY_ABS_ADDR(USB_DMA_BASE_ADDR
                                             + USB_SRAM_EP2_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP2_OUT_OFFSET, ep2_out);

    inten = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTEN);
    lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTEN,
                 inten | DEV0_CSR_INTSTAT_EP2OUT_MASK);
    VPRINTF(LOW, "MCU: EP2 OUT (ISO, single-buffer) armed for %d bytes\n",
            USB_ISO_TRANSFER_BYTES);
}

// Arm EP2 IN as isochronous, needed for the line-2211 leg (iso_in_pending_r
// = '1' at the moment a mismatching PID_OUT token arrives). Mirrors
// caliptra_ss_usb_hs_dev_err_pkt_unexpected.c's usb_ep2_in_arm_iso(): both
// buffers get USB_EP_ENTRY_ACTIVE and USB_EP_ENTRY_TYPE_PERIODIC (the
// periodic bit is what makes epinfo_iso = '1' on this endpoint - see
// usb_dma.m.vhdl "epinfo_iso <= epinfo_periodic = '1' and epinfo_rf_tv = '0'"
// - omitting it is why this endpoint previously never reached
// set_iso_in_pending at all).
static void usb_ep2_in_arm_iso(void) {
    uint32_t inten;

    for (uint32_t i = 0; i < USB_EP2_IN_NBYTES_TOTAL; i += 4) {
        uint32_t w = 0x11223344u + i;
        lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP2_IN_BUF_OFFSET + i, w);
    }

    uint32_t ep2_in_buf0 = USB_EP_ENTRY_ACTIVE
                         | USB_EP_ENTRY_TYPE_PERIODIC
                         | USB_EP_ENTRY_NBYTES(USB_EP2_IN_BUF_BYTES)
                         | USB_EP_ENTRY_ABS_ADDR(USB_DMA_BASE_ADDR
                                                  + USB_SRAM_EP2_IN_BUF_OFFSET);
    uint32_t ep2_in_buf1 = USB_EP_ENTRY_ACTIVE
                         | USB_EP_ENTRY_TYPE_PERIODIC
                         | USB_EP_ENTRY_NBYTES(USB_EP2_IN_BUF_BYTES)
                         | USB_EP_ENTRY_ABS_ADDR(USB_DMA_BASE_ADDR
                                                  + USB_SRAM_EP2_IN_BUF_OFFSET
                                                  + USB_EP2_IN_BUF_BYTES);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP2_IN_BUF0_OFFSET, ep2_in_buf0);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP2_IN_BUF1_OFFSET, ep2_in_buf1);

    inten = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTEN);
    lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTEN,
                 inten | DEV0_CSR_INTSTAT_EP2IN_MASK);
    VPRINTF(LOW, "MCU: EP2 IN (ISO) armed for %d bytes total - line-2211 leg\n",
            USB_EP2_IN_NBYTES_TOTAL);
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
    bool     ep2_armed          = false;
    bool     ep2_in_armed       = false;
    bool     host_stop_seen     = false;

    VPRINTF(LOW, "=================\nMCU: USB error injection - ISO token-direction mismatch\n=================\n\n");

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
                if (ep2_armed) {
                    // A bus reset wipes the descriptor, so the arm has to be
                    // redone once enumeration restarts.
                    ep2_armed = false;
                    VPRINTF(LOW, "MCU: Bus reset - EP2 arm cleared\n");
                }
                if (ep2_in_armed) {
                    ep2_in_armed = false;
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
                    usb_ep2_out_arm_iso();
                    ep2_armed = true;
                }
                // EP2 IN is intentionally NOT armed here - see the file
                // header's "WHY EP2 IN IS ARMED AFTER THE THIRD EP2 OUT
                // COMPLETION" note. It is armed below, after the third EP2
                // OUT completion, once the sequence's three 2192/2231/2251
                // legs are done and it is about to send the line-2211 leg's
                // IN/OUT pair.
            } else {
                // Status-stage ZLP OUT of a control read completed; re-arm
                // EP0 OUT or enumeration stalls.
                usb_ep0_arm_out();
            }
        }

        if (reg_data & DEV0_CSR_INTSTAT_EP0IN_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);
        }

        // Each of the sequence's ISO OUT data phases completes normally
        // (they arm iso_out_pending_r, they are not themselves the
        // mismatch). Re-arm EP2 OUT so the next OUT data phase in the
        // sequence has a fresh buffer.
        if (reg_data & DEV0_CSR_INTSTAT_EP2OUT_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP2OUT_MASK);
            ep2out_completions++;
            usb_ep2_out_arm_iso();

            // The sequence's three 2192/2231/2251 legs each complete one
            // ISO OUT data phase before their mismatched token. Once the
            // third one lands, the body() is about to move on to the final
            // 2211 leg (directed IN then OUT), so EP2 IN is armed now - see
            // the file header's "WHY EP2 IN IS ARMED AFTER THE THIRD EP2
            // OUT COMPLETION" note for why this cannot happen any earlier.
            if (!ep2_in_armed && ep2out_completions == 3) {
                usb_ep2_in_arm_iso();
                ep2_in_armed = true;
            }
        }

        if (poll_count % 10000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x EP2=0x%x\n",
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

    VPRINTF(LOW, "MCU: ISO token-direction mismatch: %d control transfers, %d EP2 OUT completions\n",
            transfers_handled, ep2out_completions);

    VPRINTF(LOW, "MCU: USB error injection - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
