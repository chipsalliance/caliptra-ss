//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
//
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
// Description: MCU firmware for the hub status-change interrupt endpoint test
//              (High Speed). Stimulus for coverage gap G1 of
//              docs/usb_coverage_gaps.md.
//
// WHAT THE FIRMWARE HAS TO DO HERE, AND WHAT IT DELIBERATELY DOES NOT
//
// The endpoint under test is the HUB's own status-change interrupt endpoint
// (EP1 IN of the hub device). It is driven entirely by hardware: usb_app_hw_hub
// arms it from hub_epin_enable_buffer, answers the DMA request with
// hub_epin_gnt and returns the status-change bitmap on hub_epin_rdata. There is
// no endpoint descriptor for it in the MCU's EP list and no buffer for the MCU
// to fill, so this firmware never touches that endpoint - there is nothing it
// could usefully do to it.
//
// What this firmware DOES provide is the one thing the test cannot get any
// other way: the hub_port_connect edge that produces the first status change.
//
//   hub_port_connect(0) <= dev0_usbreg_dev_connect
//       (ip_xxx_3511_hs_mem_compound_structure.a.vhdl line 2357)
//   if hub_port_connect(i) /= hub_port_connect_d(i) then
//       hub_port_connect_change(i) <= '1'
//       (usb_app_hw_hub.m.vhdl lines 202-203)
//
// boot_usb_core_hub() sets USBDC0 DEVCMDSTAT.DCON as part of its normal
// bring-up, so the 0 -> 1 edge on hub downstream port 1 happens during boot and
// hub_port_connect_change(0) is already latched by the time the host has
// finished enumerating the hub. The host sequence reads it in its first EP1 IN
// poll. No extra DCON toggling is needed and none is done: a deliberate
// hotplug cycle is the subject of
// caliptra_ss_usb_dual_device_hs_dev0_hotplug and would only make this test
// slower and harder to attribute.
//
// Everything else below is the standard bring-up plus EP0 poll loop, identical
// in shape to caliptra_ss_usb_hs_hub_endpoint_halt.c. It keeps USBDC0
// responsive while the host drives hub-class requests, and it services the bus
// reset that the host's SetPortFeature(PORT_RESET) on port 1 delivers to USBDC0
// mid-test. That port reset is expected: it is how the sequence produces
// hub_port_reset_change, which the hub only latches when the port is enabled.
// The firmware handles the resulting DEVCMDSTAT.DRES_C through
// usb_handle_bus_reset() the same way it would handle any other bus reset, and
// the test makes no claim about USBDC0 afterwards.
//
// The host sequence addresses only the hub, so no data traffic ever reaches the
// MCU. The loop therefore has no work-completion condition of its own and must
// be released by the host - see the MCU STOP handshake note below.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"
// Including mcu_isr.h is what makes the build system compile and link
// mcu_isr.o for this test (see tools/scripts/Makefile).
#include "mcu_isr.h"

// WHEN THIS FIRMWARE IS ALLOWED TO HALT.
//
// The MCU halt ends the simulation, so halting while the host sequence is
// still running turns any host-side wait into a false timeout. That is what
// the first run of this test hit: with the 5000-poll budget copied from
// caliptra_ss_usb_hs_hub_endpoint_halt - an EP0-only test that finishes early
// - the MCU halted at 567497 ns while the host was still waiting on its first
// EP1 IN poll, issued at 365866 ns. No leg ever reached a verdict.
//
// Sizing the budget to outlast the host is the wrong fix: it is a guess that
// has to be re-guessed whenever either side changes, and it silently converts
// a host-side stall into a pass or a misattributed timeout. Instead this uses
// the MCU STOP handshake already used by
// caliptra_ss_usb_fs_dev_lpm_l1_dev_wakeup and the OCP-recovery tests - the
// host holds a command on MCI GENERIC_INPUT_WIRES_1 until this firmware acks
// it on GENERIC_OUTPUT_WIRES_1, so the halt is ordered by the host rather than
// by a cycle count and EP0 stays serviced right up to that point.
//
// USB_POLL_TIMEOUT is now only a safety ceiling for the case where the STOP
// never arrives (older sequence, observer interface not wired into the TB, or
// a host-side failure earlier in the run). It must not hang the simulation, so
// the loop still gives up and halts on its own, which is the old behaviour.
#define USB_POLL_TIMEOUT 40000

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

// Storage for the symbols the ISR library declares extern.
volatile uint32_t intr_count;
volatile mcu_intr_received_s mcu_intr_rcv = {0};


#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


void main (void) {

    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t transfers_handled = 0;
    uint32_t bus_resets_seen   = 0;
    uint32_t usb_events;
    uint32_t stop_seen = 0;


    VPRINTF(LOW, "=================\nMCU: USB hub status-change interrupt endpoint test\n=================\n\n");

    // Standard MCU boot sequence
    boot_mcu();

    // Initialize USB device controller BEFORE Caliptra bringup.
    // USB PHY and pull-up need time to settle while Caliptra boots.
    // boot_usb_core_hub() calls usb_hub_init_and_connect() internally, which
    // programs the HUB RAM descriptors and sets HUB_EN only (HUB_CONNECT
    // is deliberately deferred - see the usb_hub_connect() call below). It
    // also sets USBDC0 DEVCMDSTAT.DCON, which is the hub_port_connect(0)
    // edge this test depends on.
    boot_usb_core_hub();

    // Enable the USB interrupt (PIC vector 3) now that boot_usb_core_hub() has
    // programmed INTEN and cleared any stale INTSTAT bits.
    // Deliberately not init_interrupts(): that routine also writes the MCI
    // and I3C interrupt registers, and this early its I3C write to
    // 0x200040a8 does not complete, stalling the LSU pipeline before
    // mstatus.MIE is set. init_usb_interrupts() touches only vector 3.
    intr_count = 0;
    init_usb_interrupts();

    // Caliptra core bringup

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    // USBDC0's own EP list/DEVCMDSTAT/DCON are now fully programmed (end
    // of boot_usb_core_hub()), so it is safe to connect the hub upstream:
    // usb_hub_connect() sets HUB_CONNECT, per the reference
    // BFM two-phase sequencing. Only after this call
    // will the host see the hub on the bus and begin enumerating it.
    usb_hub_connect();

    VPRINTF(LOW, "MCU: Caliptra core ready, entering USB event loop\n");

    // Read initial USB state. DEVCMDSTAT.DCON is expected set here: it is what
    // drives hub downstream port 1 connect, and therefore the first
    // status-change bit the host will read off the hub interrupt endpoint.
    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT = 0x%x\n", reg_data);
    reg_data = lsu_read_32(USB_DEV_INTSTAT);
    VPRINTF(LOW, "MCU: USB INTSTAT = 0x%x\n", reg_data);


    // --- Main USB event loop: poll for SETUP packets ---
    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {

        // Direct DEVCMDSTAT poll for bus reset (fallback - INTSTAT may not report DEV_INT)
        usb_handle_bus_reset();

        // Drain the ISR mailbox. service_usb_intr() already read and
        // acknowledged INTSTAT, so the foreground loop must not touch
        // INTSTAT itself. Snapshot then clear by complement so bits the
        // ISR sets while we are handling this batch are not lost.
        usb_events = mcu_intr_rcv.usb;
        mcu_intr_rcv.usb &= ~usb_events;

        // Check for device-level interrupts (bus reset, connect change).
        // At least one bus reset is expected mid-test: the host drives
        // SetPortFeature(PORT_RESET) on hub port 1 to produce
        // hub_port_reset_change, and that reaches USBDC0 as dev0_portreset.
        if (usb_events & DEV0_CSR_INTSTAT_DEV_INT_MASK) {

            uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
            VPRINTF(LOW, "MCU: DEV_INT - DEVCMDSTAT = 0x%x\n", cmd);
            if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
                bus_resets_seen++;
            }
            // No INTSTAT write here: service_usb_intr() already cleared it.
        }

        // Check for EP0 OUT interrupt (SETUP or data)
        if (usb_events & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);

            if (cmd & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
                // NOTE: do NOT VPRINTF before usb_handle_control_transfer.
                // Each VPRINTF adds ~1-2us; the host VIP gives up on IN
                // polling ~5us after the SETUP ACK. Logging is done inside
                // the handler AFTER the SETUP bit is cleared.
                usb_handle_control_transfer();
                transfers_handled++;
            } else {
                // Status-stage ZLP OUT for a control-read completed (no
                // SETUP set). HW cleared ACTIVE on the EP0 OUT descriptor;
                // re-arm it so the next SETUP packet is received instead
                // of NAK'd.
                usb_ep0_arm_out();
            }
        }


        // Periodic diagnostic dump
        if (poll_count % 1000 == 0 && poll_count > 0) {
            uint32_t diag_cmd     = lsu_read_32(USB_DEV_DEVCMDSTAT);
            uint32_t diag_int     = lsu_read_32(USB_DEV_INTSTAT);
            uint32_t ep0_out      = lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000);
            uint32_t ep0_in_diag  = lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008);

            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x EP0OUT=0x%x EP0IN=0x%x transfers=%d resets=%d intr_cnt=%d\n",
                    poll_count, diag_cmd, diag_int, ep0_out, ep0_in_diag,
                    transfers_handled, bus_resets_seen, intr_count);
        }

        // No mcu_sleep here: the mailbox check is a single DCCM load, so the
        // loop stays tight and USB events are picked up within ~1us of the
        // interrupt being taken.

        // Host-ordered release. The sequence holds the command asserted until
        // it sees the ack, so this poll cannot miss it. Checked last in the
        // iteration so EP0 is always serviced one more time before halting.
        {
            uint32_t command =
                lsu_read_32(SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_1);

            if ((command >> USB_LEGACY_EP0_COMMAND_MAGIC_SHIFT) ==
                    USB_LEGACY_EP0_COMMAND_MAGIC &&
                ((command >> USB_LEGACY_EP0_COMMAND_OPCODE_SHIFT) &
                    USB_LEGACY_EP0_COMMAND_NIBBLE_MASK) ==
                    USB_LEGACY_EP0_COMMAND_STOP) {

                // Ack by echoing the command with ACK_MAGIC substituted.
                lsu_write_32(SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1,
                    ((uint32_t)USB_LEGACY_EP0_COMMAND_ACK_MAGIC <<
                     USB_LEGACY_EP0_COMMAND_MAGIC_SHIFT) |
                    (command & 0x00FFFFFFu));
                stop_seen = 1u;
                VPRINTF(LOW, "MCU: host STOP received after %d polls\n",
                        poll_count + 1);
                break;
            }
        }

    }

    if (!stop_seen)
        VPRINTF(LOW, "MCU: no host STOP within %d polls; halting anyway\n",
                poll_count);

    // Report final state
    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT final = 0x%x\n", reg_data);
    reg_data = lsu_read_32(USB_DEV_INFO);
    VPRINTF(LOW, "MCU: USB INFO final = 0x%x\n", reg_data);

    VPRINTF(LOW, "MCU: USB hub status-change interrupt endpoint test - transfers handled: %d, bus resets: %d\n",
            transfers_handled, bus_resets_seen);

    VPRINTF(LOW, "MCU: USB hub status-change interrupt endpoint test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
