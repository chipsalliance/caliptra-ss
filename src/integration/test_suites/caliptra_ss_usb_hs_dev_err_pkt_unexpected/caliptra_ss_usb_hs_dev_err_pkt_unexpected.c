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
// Description: MCU firmware for caliptra_ss_usb_hs_dev_err_pkt_unexpected.
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype bin packet_unexpected (0x3), at the
// usb_pie.m.vhdl line 2879 assignment site.
//
// WHY THIS IS AN ISOCHRONOUS TEST
//
// All seven live assignment sites of 0x3 are reachable only while an
// isochronous transaction is outstanding - see the full site-by-site list in
// caliptra_ss_usb_hs_dev_err_pkt_unexpected_sequence.svh. The gating flags
// iso_in_pending_r / iso_out_pending_r are set only under
// "if epinfo_iso = '1'" (usb_pie.m.vhdl line 2500), and epinfo_iso comes from
// the endpoint type bits of the list entry this firmware writes. On a bulk
// endpoint the bin is unreachable, so EP2 is armed as isochronous here even
// though every other error suite in this family uses bulk EP1.
//
// WHY THIS SUITE DOES NOT USE usb_err_inject_fw_common.h
//
// That header exists for the wire-corruption suites, where the firmware only
// has to keep a bulk endpoint armed while the host damages packets. Here the
// firmware IS the stimulus and does the OPPOSITE of keeping the endpoint
// armed: it arms EP2 OUT exactly once and then deliberately refuses to
// re-arm it. The RTL branch being targeted is
//
//     elsif epinfo_active = '0' and crc16_valid_nxt = '1' then
//        ... else -- isochronous ep -- no handshake is returned.
//           errortype <= "0011"; --ERROR_PACKET_UNEXPECTED
//
// so the condition is a perfectly good isochronous OUT data packet arriving
// at an endpoint whose ACTIVE bit is clear. Hardware clears ACTIVE when it
// consumes the first transfer, so "arm once, never re-arm" is precisely what
// produces it on the host's second transfer.
//
// NOTHING IS CORRUPTED
//
// Both packets the host sends are well formed and the CRC16 is valid - the
// branch above even requires crc16_valid_nxt = '1'. There is no exception
// injection anywhere in this test.
//
// NO DATA CHECK
//
// The first transfer's payload is received normally and could be checked, but
// is not: the second transfer is discarded without a handshake (USB 2.0
// section 8.5.5 - isochronous transfers carry no handshake at all), so the
// buffer contents after the scenario are a mix of the first transfer's data
// and nothing. The firmware reports the ACTIVE bit state instead, which is
// the thing that actually matters for the bin.

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
// caliptra_ss_usb_hs_dev_iso_out.c so the two ISO tests agree on the SRAM
// map: the buffer at 0x600..0x9FF is 1024 bytes and sits clear of the EP0
// buffers at 0x000-0x1FF.
#define USB_SRAM_EP2_OUT_BUF_OFFSET    0x600u
#define USB_EP_LIST_EP2_OUT_OFFSET     0x020u

// HS isochronous max packet (USB 2.0 table 5-7).
#define USB_ISO_TRANSFER_BYTES         1024u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Arm EP2 OUT as isochronous: T=1 (periodic) with the RF bit clear, which is
// the ISO selector rather than the interrupt one. ABS_ADDR rather than the
// offset form, matching caliptra_ss_usb_hs_dev_iso_out.c.
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
    VPRINTF(LOW, "MCU: EP2 OUT (ISO) armed ONCE for %d bytes - it will NOT be re-armed\n",
            USB_ISO_TRANSFER_BYTES);
}

static uint32_t usb_ep2_out_read(void) {
    return lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP2_OUT_OFFSET);
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
    uint32_t ep2_completions   = 0;
    bool     ep2_armed_once    = false;
    bool     host_stop_seen    = false;

    VPRINTF(LOW, "=================\nMCU: USB error injection - unexpected packet (ISO)\n=================\n\n");

    boot_mcu();
    boot_usb_core_hub();
    usb_hub_connect();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    // There is no local completion event to stop on: the second ISO OUT is
    // meant to arrive at an un-armed endpoint and never completes, so the loop
    // used to run its whole budget out and the simtime was set by the loop
    // count rather than the stimulus. The host now releases the MCU when its
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
                if (ep2_armed_once) {
                    // A bus reset wipes the descriptor, so the one-shot arm
                    // has to be redone once enumeration restarts. This is a
                    // re-arm after a RESET, not after a completion, so it does
                    // not defeat the purpose of the test.
                    ep2_armed_once = false;
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
                if (!ep2_armed_once) {
                    usb_ep2_out_arm_iso();
                    ep2_armed_once = true;
                }
            } else {
                // Status-stage ZLP OUT of a control read completed; re-arm EP0
                // OUT or enumeration stalls after the first control read.
                usb_ep0_arm_out();
            }
        }

        if (reg_data & DEV0_CSR_INTSTAT_EP0IN_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);
        }

        // EP2 OUT completion of the FIRST transfer. The interrupt is
        // acknowledged and the descriptor is reported, but the endpoint is
        // deliberately left un-armed: that is the whole stimulus. Exactly one
        // completion is expected; a second would mean the endpoint had somehow
        // been re-armed and the bin would not close.
        if (reg_data & DEV0_CSR_INTSTAT_EP2OUT_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP2OUT_MASK);
            uint32_t ep2_entry = usb_ep2_out_read();
            uint32_t residual  = (ep2_entry >> 11) & 0x7FFFu;

            ep2_completions++;
            VPRINTF(LOW,
                "MCU: EP2 OUT (ISO) completion %d - received %d bytes, entry 0x%x (ACTIVE=%d)\n",
                ep2_completions, USB_ISO_TRANSFER_BYTES - residual, ep2_entry,
                (ep2_entry & USB_EP_ENTRY_ACTIVE) ? 1 : 0);
            VPRINTF(LOW, "MCU: leaving EP2 un-armed on purpose - the next ISO OUT must be unexpected\n");
        }

        if (poll_count % 10000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x EP2=0x%x completions=%d\n",
                    poll_count,
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT),
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT),
                    usb_ep2_out_read(), ep2_completions);
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

    VPRINTF(LOW, "MCU: unexpected packet (ISO): %d control transfers, %d EP2 completions, EP2 entry 0x%x\n",
            transfers_handled, ep2_completions, usb_ep2_out_read());

    VPRINTF(LOW, "MCU: USB error injection - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
