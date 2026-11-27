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
// Description: MCU firmware for caliptra_ss_usb_hs_dev_err_ping_stall.
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype bin sent_stall (0xA), RTL site
// usb_pie.m.vhdl line 2528 (PING to a stalled endpoint).
//
// Identical arming logic to caliptra_ss_usb_hs_dev_err_stall: EP1 OUT is
// armed with STALL set and ACTIVE clear as soon as the control pipe is
// running, and is never re-armed/unhalted. The only difference versus that
// suite is the HOST stimulus (PING instead of a bulk OUT), driven from
// caliptra_ss_usb_hs_dev_err_ping_stall_sequence. See that sequence's header
// and caliptra_ss_usb_hs_dev_err_stall.c for the RTL derivation.

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
// See caliptra_ss_usb_hs_dev_err_stall.c for why both halves are required.
static void usb_ep1_out_halt(void) {
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET,
                 USB_EP_ENTRY_STALL);
    VPRINTF(LOW, "MCU: EP1 OUT halted (STALL set, ACTIVE clear)\n");
}

// Has the host told us it is finished with the device? Same decode/ack
// shape as every other suite in this family - see
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
    bool     ep1_halted        = false;
    bool     host_stop_seen    = false;

    VPRINTF(LOW, "=================\nMCU: USB negative testing - PING to STALLed endpoint\n=================\n\n");

    boot_mcu();
    boot_usb_core_hub();
    usb_hub_connect();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

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
                if (!ep1_halted) {
                    usb_ep1_out_halt();
                    ep1_halted = true;
                }
            } else {
                usb_ep0_arm_out();
            }
        }

        if (reg_data & DEV0_CSR_INTSTAT_EP0IN_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);
        }

        // No EP1OUT handling: a halted endpoint answers a PING with a STALL
        // handshake in hardware and raises no completion interrupt.
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

        host_stop_seen = usb_err_host_stop_seen();
    }

    if (host_stop_seen)
        VPRINTF(LOW, "MCU: host STOP received after %d poll iterations; halting\n",
                poll_count);
    else
        VPRINTF(LOW, "MCU: no host STOP within %d poll iterations; halting anyway\n",
                poll_count);

    VPRINTF(LOW, "MCU: PING to STALLed endpoint: %d control transfers, EP1 halted=%d\n",
            transfers_handled, (int)ep1_halted);

    VPRINTF(LOW, "MCU: USB negative testing - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
