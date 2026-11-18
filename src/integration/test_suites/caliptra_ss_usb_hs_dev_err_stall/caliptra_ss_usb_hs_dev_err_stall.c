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
// Description: MCU firmware for caliptra_ss_usb_hs_dev_err_stall.
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype bin sent_stall (0xA).
//
// WHY THIS SUITE DOES NOT USE usb_err_inject_fw_common.h
//
// The other seven error suites share that header because for them the
// firmware is incidental: the host corrupts the wire and the firmware just
// has to keep an endpoint armed. Here the firmware IS the stimulus. The three
// live assignment sites of 0xA (usb_pie.m.vhdl lines 2391, 2528 and 2816) are
// all guarded by
//
//     elsif epinfo_stall = '1' and epinfo_active = '0' then
//        -- stall handshake must be returned
//        errortype <= "1010"; --ERROR_SENT_STALL
//
// and usb_dma.m.vhdl lines 303 and 297 latch those two signals directly out
// of the endpoint command/status list entry this firmware writes:
//
//     epinfo_active <= dma_rdata(31);   -- USB_EP_ENTRY_ACTIVE
//     epinfo_stall  <= dma_rdata(29);   -- USB_EP_ENTRY_STALL
//
// So the condition is exactly "STALL set, ACTIVE clear" in the EP1 OUT
// descriptor, and only firmware can produce it.
//
// WHY ACTIVE MUST BE CLEAR AND NOT MERELY IGNORED
//
// The RTL requires BOTH halves. Setting STALL while leaving ACTIVE set does
// not reach the errortype assignment at all - line 2495 takes a different
// branch and only raises set_ignore_data, which discards the payload while
// still handshaking normally. The arm below therefore writes STALL with no
// ACTIVE bit, which is also why no buffer address or byte count is
// meaningful: the endpoint is not going to receive anything.
//
// THE ENDPOINT IS LEFT HALTED ON PURPOSE
//
// USB 2.0 section 8.4.5 defines a functional stall as persisting until the
// host clears it with CLEAR_FEATURE(ENDPOINT_HALT). This firmware never
// clears it, so there is no recovery transfer in the matching sequence - see
// caliptra_ss_usb_hs_dev_err_stall_sequence.svh. Clearing it here would race
// the host and could retire the halt before the OUT even arrived.

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
#define USB_POLL_TIMEOUT             60000u

// EP command/status list offset of the EP1 OUT descriptor. Same value every
// other EP1 OUT test uses.
#define USB_EP_LIST_EP1_OUT_OFFSET   0x010u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Arm EP1 OUT in the halted state: STALL set, ACTIVE deliberately NOT set.
// See the file header for why both halves are required.
static void usb_ep1_out_halt(void) {
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET,
                 USB_EP_ENTRY_STALL);
    VPRINTF(LOW, "MCU: EP1 OUT halted (STALL set, ACTIVE clear)\n");
}

// Has the host told us it is finished with the device?
//
// Reuses the MCI generic-wire command channel from the OCP-recovery work, the
// same decode and ack shape as caliptra_ss_usb_fs_dev_lpm_l1_dev_wakeup: the
// command arrives on GENERIC_INPUT_WIRES_1 as magic[31:24] | opcode[23:20] |
// delta[19:16] | generation[15:0], and the ack goes back on
// GENERIC_OUTPUT_WIRES_1 with ACK_MAGIC substituted for MAGIC. The host holds
// the command asserted until it sees the ack, so this poll cannot miss it.
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
    bool     ep1_halted        = false;
    bool     host_stop_seen    = false;

    VPRINTF(LOW, "=================\nMCU: USB error injection - device endpoint STALL\n=================\n\n");

    boot_mcu();
    boot_usb_core_hub();
    usb_hub_connect();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    // There is no local completion event to stop on: a halted endpoint never
    // completes a transfer by design, so the loop used to run its whole budget
    // out and the simtime was set by the loop count rather than the stimulus.
    // The host now releases the MCU when its checks are done.
    for (poll_count = 0;
         poll_count < USB_POLL_TIMEOUT && !host_stop_seen;
         poll_count++) {

        usb_handle_bus_reset();
        reg_data = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT);

        if (reg_data & DEV0_CSR_INTSTAT_DEV_INT_MASK) {
            uint32_t cmd = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
            if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
                if (ep1_halted) {
                    // A bus reset clears the descriptor, so the halt has to be
                    // re-applied once enumeration restarts.
                    ep1_halted = false;
                    VPRINTF(LOW, "MCU: Bus reset - EP1 halt cleared\n");
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
                // Halt EP1 as soon as the control pipe is running, which is
                // well before the host finishes enumerating and sends the OUT.
                if (!ep1_halted) {
                    usb_ep1_out_halt();
                    ep1_halted = true;
                }
            } else {
                // Status-stage ZLP OUT of a control read completed; re-arm EP0
                // OUT or enumeration stalls. Same note as every other USB
                // device firmware in this tree.
                usb_ep0_arm_out();
            }
        }

        if (reg_data & DEV0_CSR_INTSTAT_EP0IN_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);
        }

        // There is deliberately NO EP1OUT handling here. A halted endpoint
        // answers in hardware with a STALL handshake and raises no completion
        // interrupt, because no transfer ever completed. If an EP1OUT
        // interrupt did appear it would mean the halt had not taken effect, so
        // it is reported rather than silently consumed.
        if (reg_data & DEV0_CSR_INTSTAT_EP1OUT_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP1OUT_MASK);
            VPRINTF(LOW,
                "MCU: UNEXPECTED EP1 OUT completion on a halted endpoint - EP entry 0x%x\n",
                lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET));
        }

        if (poll_count % 10000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x EP1=0x%x halted=%d\n",
                    poll_count,
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT),
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT),
                    lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET),
                    (int)ep1_halted);
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

    VPRINTF(LOW, "MCU: device endpoint STALL: %d control transfers, EP1 halted=%d\n",
            transfers_handled, (int)ep1_halted);

    VPRINTF(LOW, "MCU: USB error injection - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
