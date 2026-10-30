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
// Description: USB hub CONFIGURATION / OTHER_SPEED_CONFIGURATION descriptor
//              test for Caliptra Subsystem (High Speed)
//
//  Boots the MCU, initializes the USB device controller (EP list, SRAM
//  buffers, DEVCMDSTAT), then brings up Caliptra core. Polls for SETUP
//  packets from the UVM VIP host and handles control transfers via the USB
//  driver library.
//
//  This is the same event loop as caliptra_ss_usb_init. The protocol
//  exercised by this test (GET_DESCRIPTOR(CONFIGURATION) and
//  GET_DESCRIPTOR(OTHER_SPEED_CONFIGURATION) directed at the hub at address 1)
//  is answered entirely by the hub-composite RTL ROM, not by firmware. No
//  test-specific firmware logic is needed here beyond the standard poll loop
//  that keeps USBDC1 enumerated behind the hub.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"
// Including mcu_isr.h is what makes the build system compile and link
// mcu_isr.o for this test (see tools/scripts/Makefile). This test is built
// with -DUSB_HUB_COMPOUND_DEV1_IRQ, which makes init_usb_interrupts() enable
// PIC vector 6 (USBDC1's looped IRQ) and mcu_isr.h compile in
// service_usb_dev1_intr() plus the mcu_intr_rcv.usb_dev1 mailbox field.
//
// This test deliberately does NOT use -DUSB_DEV_SEL=1. USBDC1 is selected at
// RUNTIME instead (see usb_select_device(1) below and the base retargeting
// that follows this include). The reason is that service_usb_intr(), the
// vector 3 handler, is an inline function defined in mcu_isr.h and resolves
// USB_DEV_INTSTAT / USB_DEV_INTEN through the compile-time USB_DEV_SEL
// aliases. Vector 3 is hard wired to USBDC0's usb_dev_irq in
// caliptra_ss_top.sv, so under -DUSB_DEV_SEL=1 that handler would read and
// write-1-to-clear USBDC1's INTSTAT from USBDC0's vector. It would then
// publish the result into mcu_intr_rcv.usb while this test polls
// mcu_intr_rcv.usb_dev1, silently consuming USBDC1's EP0OUT SETUP events and
// hanging the control transfer. Dropping USB_DEV_SEL keeps vector 3 pointed
// at USBDC0 and leaves USBDC1 to vector 6, which already addresses
// SOC_USB_DEV1_CSR_BASE_ADDR explicitly. This matches the configuration used
// by the passing caliptra_ss_usb_dual_device_hs_bulk_loopback test.
#include "mcu_isr.h"

// -----------------------------------------------------------------------------
// Runtime device retargeting for THIS translation unit.
//
// usb.h resolves the device-neutral USB_DEV_* register macros and
// USB_DEV_DMA_BASE_ADDR against the COMPILE-TIME base selected by USB_DEV_SEL
// (now left at its default 0 = USBDC0). usb.c re-points those same macros at
// usb_select_device()'s RUNTIME choice, but that #undef/#define is scoped to
// usb.c's translation unit only. The code in THIS file reads USB_DEV_* and
// USB_DEV_DMA_BASE_ADDR directly, so without the same retargeting here it
// would address USBDC0 while the test is driving USBDC1.
//
// Re-apply usb.c's exact trick: re-define the two base macros in terms of the
// runtime accessors usb_active_dev_csr_base() / usb_active_dev_mem_base()
// (exported from usb.c). Every derived macro in usb.h is expanded at its USE
// site, so re-pointing the bases makes all of them follow
// usb_select_device() in this file too.
//
// This block MUST stay AFTER #include "mcu_isr.h". service_usb_intr() is an
// inline function defined in that header and is macro-expanded at its point
// of definition; retargeting before the include would make the vector 3
// handler follow usb_select_device(1) and re-create the aliasing described
// above.
#undef USB_DEV_CSR_BASE_ADDR
#undef USB_DEV_MEM_BASE_ADDR
#define USB_DEV_CSR_BASE_ADDR  usb_active_dev_csr_base()
#define USB_DEV_MEM_BASE_ADDR  usb_active_dev_mem_base()


#define USB_POLL_TIMEOUT 10000


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


    VPRINTF(LOW, "=================\nMCU: USB hub_config_descriptor test\n=================\n\n");

    // Standard MCU boot sequence
    boot_mcu();

    // Retarget the shared USB library at USBDC1 (device1) for the rest of the
    // run. This replaces the former -DUSB_DEV_SEL=1 compile-time pinning; see
    // the rationale above #include "mcu_isr.h". It must happen BEFORE
    // boot_usb_core_hub() so the EP list, DEVCMDSTAT and INTEN programming all
    // land in USBDC1's aperture. The #define retargeting at the top of this
    // file makes the USB_DEV_* reads below follow this selection too.
    usb_select_device(1);

    // Initialize USB device controller BEFORE Caliptra bringup.

    // USB PHY and pull-up need time to settle while Caliptra boots.
    // boot_usb_core_hub() calls usb_hub_init_and_connect() internally, which
    // programs the HUB RAM descriptors and sets HUB_EN only (HUB_CONNECT
    // is deliberately deferred - see the usb_hub_connect() call below).
    boot_usb_core_hub();

    // Enable the USB interrupts now that boot_usb_core_hub() has programmed
    // INTEN and cleared any stale INTSTAT bits. This is a USBDC1 (dev1) test
    // built with -DUSB_HUB_COMPOUND_DEV1_IRQ, so init_usb_interrupts() enables
    // PIC vector 6 (USBDC1's looped IRQ) in addition to vector 3. USBDC1's EP0
    // SETUP events are therefore delivered to the mcu_intr_rcv.usb_dev1 mailbox.
    // Deliberately not init_interrupts(): that routine also writes the MCI
    // and I3C interrupt registers, and this early its I3C write to
    // 0x200040a8 does not complete, stalling the LSU pipeline before
    // mstatus.MIE is set. init_usb_interrupts() touches only the USB vectors.

    intr_count = 0;
    init_usb_interrupts();

    // Caliptra core bringup

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    // USBDC1's own EP list/DEVCMDSTAT/DCON are now fully programmed (end
    // of boot_usb_core_hub()), so it is safe to connect the hub upstream:
    // usb_hub_connect() sets HUB_CONNECT, per the reference
    // BFM two-phase sequencing. Only after this call
    // will the host see the hub on the bus and begin enumerating its
    // downstream port (where USBDC1 is attached).
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

        // Drain the ISR mailbox. This is a USBDC1 (dev1) test whose IRQ is on
        // PIC vector 6, so events are published to the usb_dev1 mailbox field
        // (filled by service_usb_dev1_intr()), NOT the usb field (vector 3 /
        // USBDC0). service_usb_dev1_intr() already read and acknowledged
        // INTSTAT, so the foreground loop must not touch INTSTAT itself.
        // Atomically snapshot and clear the ISR mailbox, preserving prior MIE.
        {
            uint32_t saved_mstatus;
            __asm__ volatile ("csrrc %0, mstatus, %1"
                              : "=r" (saved_mstatus)
                              : "r" (0x8u)
                              : "memory");
            usb_events = mcu_intr_rcv.usb_dev1;
            mcu_intr_rcv.usb_dev1 = 0;
            if (saved_mstatus & 0x8u) {
                __asm__ volatile ("csrrs zero, mstatus, %0"
                                  :
                                  : "r" (0x8u)
                                  : "memory");
            }
        }


        // Check for device-level interrupts (bus reset, connect change)
        if (usb_events & DEV0_CSR_INTSTAT_DEV_INT_MASK) {

            uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
            VPRINTF(LOW, "MCU: DEV_INT - DEVCMDSTAT = 0x%x\n", cmd);
            if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
            }
            // No INTSTAT write here: service_usb_dev1_intr() already cleared it.

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

    VPRINTF(LOW, "MCU: USB hub_config_descriptor test - transfers handled: %d\n", transfers_handled);

    VPRINTF(LOW, "MCU: USB hub_config_descriptor test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
