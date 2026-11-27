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
// Description: MCU firmware for caliptra_ss_usb_hs_dev_err_iso_stalled.
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype bin packet_unexpected (0x3), at the
// usb_pie.m.vhdl line 2837 assignment site (the ISO sibling of the bulk
// STALL site caliptra_ss_usb_hs_dev_err_stall closes at line 2816).
//
// WHY THIS SUITE DOES NOT USE usb_err_inject_fw_common.h
//
// Same reason as caliptra_ss_usb_hs_dev_err_stall: epinfo_stall and
// epinfo_active are not bus-visible, they are latched straight out of the
// EP2 OUT command/status list entry this firmware writes (usb_dma.m.vhdl
// lines 303/297). The firmware IS the stimulus here, not the host.
//
// WHY THE ENDPOINT IS ALSO MARKED ISOCHRONOUS
//
// usb_pie.m.vhdl line 2837 is reached only when iso_out_pending_r = '1' at
// the same time epinfo_stall = '1' and epinfo_active = '0'; the bulk-endpoint
// sibling (iso_out_pending_r = '0') takes line 2816 instead, which err_stall
// already closes. iso_out_pending_r is set from epinfo_iso = '1' as soon as
// the OUT data packet is accepted (usb_pie.m.vhdl lines 2498-2503), so this
// firmware arms EP2 OUT with USB_EP_ENTRY_TYPE_PERIODIC | USB_EP_ENTRY_RF_ISO
// in addition to STALL, with ACTIVE deliberately clear - the same two control
// bits err_stall sets on EP1, plus the ISO type bits so epinfo_iso = '1'.
//
// THE ENDPOINT IS LEFT HALTED ON PURPOSE
//
// Same rationale as err_stall: there is no recovery leg in the matching
// sequence, so this firmware never clears the halt.

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

// EP2 OUT list offset, same SRAM map as caliptra_ss_usb_hs_dev_err_pkt_unexpected.
#define USB_EP_LIST_EP2_OUT_OFFSET   0x020u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Arm EP2 OUT in the halted state: isochronous type bits set, STALL set,
// ACTIVE deliberately NOT set. See the file header for why both the type
// bits and both control bits are required.
static void usb_ep2_out_halt_iso(void) {
    uint32_t ep2_out = USB_EP_ENTRY_STALL
                      | USB_EP_ENTRY_TYPE_PERIODIC
                      | USB_EP_ENTRY_RF_ISO;
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP2_OUT_OFFSET, ep2_out);
    VPRINTF(LOW, "MCU: EP2 OUT (ISO) halted (STALL set, ACTIVE clear)\n");
}

// Has the host told us it is finished with the device?
//
// Same MCI generic-wire command channel as the rest of this family - see
// caliptra_ss_usb_hs_dev_err_stall.c for the full note.
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
    bool     ep2_halted        = false;
    bool     host_stop_seen    = false;

    VPRINTF(LOW, "=================\nMCU: USB negative testing - ISO endpoint STALL\n=================\n\n");

    boot_mcu();
    boot_usb_core_hub();
    usb_hub_connect();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    // There is no local completion event to stop on: a halted endpoint never
    // completes a transfer by design. The host releases the MCU when its
    // checks are done.
    for (poll_count = 0;
         poll_count < USB_POLL_TIMEOUT && !host_stop_seen;
         poll_count++) {

        usb_handle_bus_reset();
        reg_data = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT);

        if (reg_data & DEV0_CSR_INTSTAT_DEV_INT_MASK) {
            uint32_t cmd = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
            if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
                if (ep2_halted) {
                    // A bus reset clears the descriptor, so the halt has to
                    // be re-applied once enumeration restarts.
                    ep2_halted = false;
                    VPRINTF(LOW, "MCU: Bus reset - EP2 halt cleared\n");
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
                // Halt EP2 as soon as the control pipe is running, which is
                // well before the host finishes enumerating and sends the
                // ISO OUT.
                if (!ep2_halted) {
                    usb_ep2_out_halt_iso();
                    ep2_halted = true;
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

        // There is deliberately NO EP2OUT handling here. A halted endpoint
        // answers with silence (isochronous transfers carry no handshake at
        // all - USB 2.0 section 8.5.5) and raises no completion interrupt,
        // because no transfer ever completed. If an EP2OUT interrupt did
        // appear it would mean the halt had not taken effect.
        if (reg_data & DEV0_CSR_INTSTAT_EP2OUT_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP2OUT_MASK);
            VPRINTF(LOW,
                "MCU: UNEXPECTED EP2 OUT (ISO) completion on a halted endpoint - EP entry 0x%x\n",
                lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP2_OUT_OFFSET));
        }

        if (poll_count % 10000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x EP2=0x%x halted=%d\n",
                    poll_count,
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT),
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT),
                    lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP2_OUT_OFFSET),
                    (int)ep2_halted);
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

    VPRINTF(LOW, "MCU: ISO endpoint STALL: %d control transfers, EP2 halted=%d\n",
            transfers_handled, (int)ep2_halted);

    VPRINTF(LOW, "MCU: USB negative testing - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
