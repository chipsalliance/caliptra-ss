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
// Description: MCU firmware for caliptra_ss_usb_hs_dev_err_iso_pid_seq.
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype bin pid_unknown (0x2), at the
// usb_pie.m.vhdl line 2632 assignment site (PID_MDATA unexpected on a
// single-transaction isochronous OUT endpoint).
//
// WHY THIS SUITE DOES NOT USE usb_err_inject_fw_common.h
//
// Same reason as caliptra_ss_usb_hs_dev_err_pkt_unexpected: the firmware's
// only job is to arm EP2 OUT as isochronous ONCE and then get out of the way.
// The actual stimulus (a directed OUT token followed by a bare MDATA data
// packet, no exception, no transfer-level API) is driven entirely by
// caliptra_ss_usb_hs_dev_err_iso_pid_seq_sequence on the packet sequencer -
// see that file's header for why the VIP transfer layer cannot express an
// MDATA PID on a non-high-bandwidth endpoint.
//
// WHY THE FIRMWARE NEVER SEES AN EP2OUT COMPLETION
//
// usb_pie.m.vhdl's PID_MDATA-unexpected branch (line 2632) clears
// iso_out_pending_r/iso_in_pending_r and returns the protocol FSM straight to
// USB_PROT_WF_IDLE without ever reaching the DMA handoff that would raise
// DEV0_CSR_INTSTAT_EP2OUT. So this firmware arms EP2 OUT exactly once, for
// the host to target, and otherwise just keeps EP0 serviced until the host
// says it is done - there is no "transfer completed" event to react to.

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
// caliptra_ss_usb_hs_dev_err_pkt_unexpected.c so the ISO tests in this
// family agree on the SRAM map.
#define USB_SRAM_EP2_OUT_BUF_OFFSET    0x600u
#define USB_EP_LIST_EP2_OUT_OFFSET     0x020u

// Deliberately one byte under the HS isochronous max packet (USB 2.0 table
// 5-7, 1024 bytes). usb_pie.m.vhdl loads iso_transact_cnt_down from
// epinfo_nbytes(11 downto 10) (see the RTL assignment near
// USB_PROT_OUT_SETUP_WF_EP_INFO_VALID / load_iso_transact_cnt_down, line
// ~3911 of usb_pie.m.vhdl): NBYTES=1024 ("010000000000") has bits [11:10] =
// "01", which lands in the TWO-transaction high-bandwidth bucket rather than
// the single-transaction "00" bucket this test needs - PID_MDATA is then
// legal as the first of two HBW transactions and pid_unknown (0x2) never
// fires. NBYTES=1023 ("001111111111") has bits [11:10] = "00", matching the
// single-buffer, non-high-bandwidth endpoint the test is actually modeling.
// The MDATA packet's PID is checked before any payload byte is consumed, so
// the sequence's 1024-byte MDATA payload is unaffected by this one-byte
// reduction in the armed buffer size.
#define USB_ISO_TRANSFER_BYTES         1023u


volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Arm EP2 OUT as isochronous: T=1 (periodic) with the RF bit clear, which is
// the ISO selector rather than the interrupt one. Single buffer entry, so
// this is NOT a high-bandwidth endpoint - the whole point of the test.
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

    VPRINTF(LOW, "=================\nMCU: USB negative testing - ISO out-of-sequence MDATA\n=================\n\n");

    boot_mcu();
    boot_usb_core_hub();
    usb_hub_connect();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    // There is no local completion event to stop on: the directed MDATA
    // packet the host sends is expected to be discarded by the RTL before
    // any DMA/interrupt is raised. The host releases the MCU when its checks
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
            } else {
                // Status-stage ZLP OUT of a control read completed; re-arm
                // EP0 OUT or enumeration stalls.
                usb_ep0_arm_out();
            }
        }

        if (reg_data & DEV0_CSR_INTSTAT_EP0IN_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);
        }

        // EP2 OUT completion would mean the RTL actually accepted the MDATA
        // data phase as a normal transfer - that would mean the bin did NOT
        // close. Logged, not treated as fatal, so the errortype checker's
        // verdict is the single source of truth.
        if (reg_data & DEV0_CSR_INTSTAT_EP2OUT_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP2OUT_MASK);
            ep2_completions++;
            VPRINTF(LOW,
                "MCU: UNEXPECTED EP2 OUT (ISO) completion %d - entry 0x%x. If this appears, the MDATA packet was accepted as ordinary data and the pid_unknown bin likely did not close.\n",
                ep2_completions, usb_ep2_out_read());
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

    VPRINTF(LOW, "MCU: ISO out-of-sequence MDATA: %d control transfers, %d unexpected EP2 completions\n",
            transfers_handled, ep2_completions);

    VPRINTF(LOW, "MCU: USB negative testing - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
