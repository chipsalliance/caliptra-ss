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
// Description: USB GetDescriptor(DEVICE) test for Caliptra Subsystem (High Speed)
//
//  Boots the MCU, initializes the USB device controller (EP list, SRAM
//  buffers, DEVCMDSTAT), then brings up Caliptra core. Polls DEVCMDSTAT
//  directly for SETUP packets from the UVM VIP host and services EP0 control
//  transfers via the shared usb.c dispatcher (no interrupt machinery).
//
//  The protocol exercised by this test (standard GET_DESCRIPTOR(DEVICE),
//  wValue=0x0100, wLength=18, issued to both the hub at address 1 and dev1
//  at address 2) is all handled inside the shared usb.c control-transfer
//  dispatcher: usb_handle_control_transfer() returns the 18-byte device
//  descriptor for a standard GET_DESCRIPTOR(DEVICE) request. No test-specific
//  firmware logic is needed here beyond the standard poll loop.
//
//  Structured to mirror caliptra_ss_usb_fs_conn.c: this is a pure polling
//  test with no ISR involvement (no mcu_isr.h, no init_usb_interrupts(), no
//  ISR mailbox). SETUP packets are detected by reading DEVCMDSTAT.SETUP
//  directly.

// -----------------------------------------------------------------------------
// USBDC1 (device1) variant of caliptra_ss_usb_hs_dev_get_device_descriptor.
// The firmware source is functionally unchanged from the USBDC0 test: the
// shared USB library is retargeted to the USBDC1 aperture (regs 0x2001_0000,
// DMA 0x2001_0100) purely by -DUSB_DEV_SEL=1, which the yml passes through
// BUILD_CFLAGS. See the USB_DEV_SEL block in
// src/integration/test_suites/libs/usb/usb.h and
// claude_md/15_usb_dev1_replication.md. Only the VPRINTF test-name strings
// are relabelled to dev1 for log clarity.
// -----------------------------------------------------------------------------
#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

#define USB_POLL_TIMEOUT 10000

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


void main (void) {

    uint32_t reg_data;
    uint32_t intstat;
    uint32_t poll_count;
    uint32_t transfers_handled = 0;


    VPRINTF(LOW, "=================\nMCU: USB dev1 get_device_descriptor test\n=================\n\n");

    // Standard MCU boot sequence
    boot_mcu();

    // Initialize USB device controller BEFORE Caliptra bringup.
    // USB PHY and pull-up need time to settle while Caliptra boots.
    // boot_usb_core() calls usb_hub_init_and_connect() internally, which
    // programs the HUB RAM descriptors and sets HUB_EN only (HUB_CONNECT
    // is deliberately deferred - see the usb_hub_connect() call below).
    boot_usb_core();

    // USBDC1's own EP list/DEVCMDSTAT/DCON are now fully programmed (end
    // of boot_usb_core()), so it is safe to connect the hub upstream:
    // usb_hub_connect() sets HUB_CONNECT, per the reference
    // janus_hub_ctrl_bfm.sv two-phase sequencing. Only after this call
    // will the host see the hub on the bus and begin enumerating its
    // downstream port (where USBDC1 is attached).
    usb_hub_connect();

    // Caliptra core bringup

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra core ready, entering USB event loop\n");

    // Read initial USB state
    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT = 0x%x\n", reg_data);
    reg_data = lsu_read_32(USB_DEV_INTSTAT);
    VPRINTF(LOW, "MCU: USB INTSTAT = 0x%x\n", reg_data);


    // --- Main USB event loop: poll INTSTAT for USB events ---
    //
    // Canonical Category-B pure-polling loop (see
    // claude_md/17_usb_polling_intstat_clearing.md): read INTSTAT each
    // iteration and write-1-to-clear each serviced bit (DEV_INT, EP0OUT,
    // EP0IN). boot_usb_core() enables DEV_INT|EP0OUT|EP0IN in INTEN, and
    // usb.c only clears EP0IN, so gating solely on DEVCMDSTAT.SETUP (the old
    // loop) left EP0OUT/DEV_INT permanently asserting dev1_usb_irq.
    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {

        // Direct DEVCMDSTAT poll for bus reset (fallback path; DEV_INT is
        // also cleared below when observed in INTSTAT).
        usb_handle_bus_reset();

        reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
        intstat  = lsu_read_32(USB_DEV_INTSTAT);

        // Device-level interrupt (bus reset / connect change). W1C DEV_INT.
        if (intstat & USBHSD_INTSTAT_DEV_INT_MASK) {
            if (reg_data & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
            }
            lsu_write_32(USB_DEV_INTSTAT, USBHSD_INTSTAT_DEV_INT_MASK);
        }

        // EP0 OUT interrupt (SETUP or status-stage OUT). W1C EP0OUT first,
        // then service the SETUP packet if DEVCMDSTAT.SETUP is set. Do not
        // VPRINTF before usb_handle_control_transfer(): each VPRINTF adds
        // ~1-2us and the host VIP gives up on IN polling ~5us after the
        // SETUP ACK. Logging happens inside the handler after the SETUP bit
        // is cleared.
        if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(USB_DEV_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();
                transfers_handled++;
            } else {
                // Status-stage ZLP OUT completed (no SETUP). HW cleared the
                // EP0 OUT ACTIVE bit; re-arm it so the next SETUP is received
                // rather than NAKed.
                usb_ep0_arm_out();
            }
        }

        // EP0 IN interrupt (control-read data / status stage). W1C EP0IN.
        if (intstat & USBHSD_INTSTAT_EP0IN_MASK) {
            lsu_write_32(USB_DEV_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);
        }

        // Periodic diagnostic dump
        if (poll_count % 1000 == 0 && poll_count > 0) {
            uint32_t diag_cmd     = lsu_read_32(USB_DEV_DEVCMDSTAT);
            uint32_t diag_int     = lsu_read_32(USB_DEV_INTSTAT);
            uint32_t ep0_out      = lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000);
            uint32_t ep0_in_diag  = lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008);

            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x EP0OUT=0x%x EP0IN=0x%x transfers=%d\n",
                    poll_count, diag_cmd, diag_int, ep0_out, ep0_in_diag, transfers_handled);
        }
    }

    // Report final state
    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT final = 0x%x\n", reg_data);
    reg_data = lsu_read_32(USB_DEV_INFO);
    VPRINTF(LOW, "MCU: USB INFO final = 0x%x\n", reg_data);

    VPRINTF(LOW, "MCU: USB dev1 get_device_descriptor test - transfers handled: %d\n", transfers_handled);

    VPRINTF(LOW, "MCU: USB dev1 get_device_descriptor test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
