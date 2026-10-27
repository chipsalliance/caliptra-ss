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
// Description: USB GET_STATUS test for Caliptra Subsystem (High Speed)
//
//  Boots the MCU, initializes the USB device controller (EP list, SRAM
//  buffers, DEVCMDSTAT), then brings up Caliptra core. Polls for SETUP
//  packets from the UVM VIP host and handles control transfers via the USB
//  driver library.
//
//  This is the same event loop as caliptra_ss_usb_init. The protocol
//  exercised by this test (SetFeature/ClearFeature(DEVICE_REMOTE_WAKEUP) +
//  GET_STATUS for the hub and dev0) is all handled inside the shared usb.c
//  control-transfer dispatcher: usb_handle_control_transfer() honors
//  SET_FEATURE(DEVICE_REMOTE_WAKEUP) by setting a shadow flag and
//  CLEAR_FEATURE by clearing it, and a subsequent GET_STATUS returns 0x0002
//  (bit1 = Remote-Wakeup) or 0x0000 accordingly. No test-specific firmware
//  logic is needed here beyond the standard poll loop.

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

#define USB_POLL_TIMEOUT 5000

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
    uint32_t usb_events;


    VPRINTF(LOW, "=================\nMCU: USB get_status test\n=================\n\n");

    // Standard MCU boot sequence
    boot_mcu();

    // Initialize USB device controller BEFORE Caliptra bringup.
    // USB PHY and pull-up need time to settle while Caliptra boots.
    // boot_usb_core_hub() calls usb_hub_init_and_connect() internally, which
    // programs the HUB RAM descriptors and sets HUB_EN only (HUB_CONNECT
    // is deliberately deferred - see the usb_hub_connect() call below).
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
    // will the host see the hub on the bus and begin enumerating its
    // downstream port (where USBDC0 is attached).
    usb_hub_connect();

    VPRINTF(LOW, "MCU: Caliptra core ready, entering USB event loop\n");

    // Read initial USB state
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
        //
        // The snapshot plus clear is a read-modify-write (lw / and / sw) on
        // a location the ISR also updates with |=. If the USB interrupt is
        // taken between the lw and the sw, the bit the ISR just published is
        // overwritten by the stale value and lost for good, because
        // service_usb_intr() has already W1C'd INTSTAT so the hardware
        // source never refires. That loses one EP0OUT event and the SETUP
        // then sits in DEVCMDSTAT forever. Mask mstatus.MIE (bit 3) across
        // the pair to make it atomic, and restore only if it was set.
        {
            uint32_t prev_mstatus = csr_read_clr_bits_mstatus(0x8u);
            usb_events = mcu_intr_rcv.usb;
            mcu_intr_rcv.usb &= ~usb_events;
            if (prev_mstatus & 0x8u) {
                csr_set_bits_mstatus(0x8u);
            }
        }

        // Check for device-level interrupts (bus reset, connect change)
        if (usb_events & DEV0_CSR_INTSTAT_DEV_INT_MASK) {

            uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
            VPRINTF(LOW, "MCU: DEV_INT - DEVCMDSTAT = 0x%x\n", cmd);
            if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
            }
            // No INTSTAT write here: service_usb_intr() already cleared it.
        }

        // Check for EP0 OUT work: either the ISR reported an EP0OUT event,
        // or the hardware is holding DEVCMDSTAT.SETUP. The second condition
        // is the recovery path: DEVCMDSTAT.SETUP is a sticky hardware flag
        // that only firmware clears (usb_clear_setup_bit()), so polling it
        // directly means a lost or coalesced EP0OUT mailbox bit can no
        // longer wedge the loop. Dispatching on the register rather than on
        // the event makes the handling idempotent and self healing.
        {
            uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
            uint32_t ep0out_evt = usb_events & DEV0_CSR_INTSTAT_EP0OUT_MASK;
            uint32_t setup_pend = cmd & DEV0_CSR_DEVCMDSTAT_SETUP_MASK;

            if (setup_pend) {
                // NOTE: do NOT VPRINTF before usb_handle_control_transfer.
                // Each VPRINTF adds ~1-2us; the host VIP gives up on IN
                // polling ~5us after the SETUP ACK. Logging is done inside
                // the handler AFTER the SETUP bit is cleared.
                usb_handle_control_transfer();
                transfers_handled++;
            } else if (ep0out_evt) {
                // Status-stage ZLP OUT for a control-read completed (no
                // SETUP set). HW cleared ACTIVE on the EP0 OUT descriptor;
                // re-arm it so the next SETUP packet is received instead
                // of NAK'd. Matches BFM:
                // dma_write32(EP0_OUT_DESC, 0xa0000000). Without this the
                // hub-composite IP's EP-list SRAM keeps EP0 OUT disarmed
                // after the first status-stage ZLP and every subsequent
                // SETUP is silently dropped (checklist item 9).
                usb_ep0_arm_out();
            }
        }


        // Periodic diagnostic dump
        if (poll_count % 1000 == 0 && poll_count > 0) {
            uint32_t diag_cmd     = lsu_read_32(USB_DEV_DEVCMDSTAT);
            uint32_t diag_int     = lsu_read_32(USB_DEV_INTSTAT);
            uint32_t ep0_out      = lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000);
            uint32_t ep0_in_diag  = lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008);

            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x EP0OUT=0x%x EP0IN=0x%x transfers=%d intr_cnt=%d\n",
                    poll_count, diag_cmd, diag_int, ep0_out, ep0_in_diag, transfers_handled, intr_count);
        }

        // No mcu_sleep here: the mailbox check is a single DCCM load, so the
        // loop stays tight and USB events are picked up within ~1us of the
        // interrupt being taken.

    }

    // Report final state
    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT final = 0x%x\n", reg_data);
    reg_data = lsu_read_32(USB_DEV_INFO);
    VPRINTF(LOW, "MCU: USB INFO final = 0x%x\n", reg_data);

    VPRINTF(LOW, "MCU: USB get_status test - transfers handled: %d\n", transfers_handled);

    VPRINTF(LOW, "MCU: USB get_status test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
