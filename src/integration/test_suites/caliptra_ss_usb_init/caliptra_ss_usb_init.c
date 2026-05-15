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
// Description: USB device controller initialization test for Caliptra Subsystem
//
//  Boots the MCU, initializes USB device controller (EP list, SRAM buffers,
//  DEVCMDSTAT), then brings up Caliptra core. Polls for SETUP packets from
//  the UVM VIP host and handles control transfers via the USB driver library.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

#define USB_POLL_TIMEOUT 20000

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


void main (void) {

    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t transfers_handled = 0;

    VPRINTF(LOW, "=================\nMCU: USB init test\n=================\n\n");

    // Standard MCU boot sequence
    boot_mcu();

    // Initialize USB device controller BEFORE Caliptra bringup.
    // USB PHY and pull-up need time to settle while Caliptra boots.
    boot_usb_core();

    // Caliptra core bringup
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra core ready, entering USB event loop\n");

    // Read initial USB state
    reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT = 0x%x\n", reg_data);
    reg_data = lsu_read_32(SOC_USBHSD_INTSTAT);
    VPRINTF(LOW, "MCU: USB INTSTAT = 0x%x\n", reg_data);

    // --- Main USB event loop: poll for SETUP packets ---
    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {

        // Direct DEVCMDSTAT poll for bus reset (fallback - INTSTAT may not report DEV_INT)
        usb_handle_bus_reset();

        // Check for device-level interrupts (bus reset, connect change)
        reg_data = lsu_read_32(SOC_USBHSD_INTSTAT);
        if (reg_data & USBHSD_INTSTAT_DEV_INT_MASK) {
            uint32_t cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
            VPRINTF(LOW, "MCU: DEV_INT - DEVCMDSTAT = 0x%x\n", cmd);
            if (cmd & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
            }
            // Clear DEV_INT
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_DEV_INT_MASK);
        }

        // Check for EP0 OUT interrupt (SETUP or data)
        if (reg_data & USBHSD_INTSTAT_EP0OUT_MASK) {
            // Clear the EP0OUT interrupt
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);

            uint32_t cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
            if (cmd & USBHSD_DEVCMDSTAT_SETUP_MASK) {
                // NOTE: do NOT VPRINTF before usb_handle_control_transfer.
                // Each VPRINTF adds ~1-2us; the host VIP gives up on IN
                // polling ~5us after the SETUP ACK. Logging is done inside
                // the handler AFTER the SETUP bit is cleared.
                usb_handle_control_transfer();
                transfers_handled++;
            }
        }

        // Periodic diagnostic dump
        if (poll_count % 1000 == 0 && poll_count > 0) {
            uint32_t diag_cmd     = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
            uint32_t diag_int     = lsu_read_32(SOC_USBHSD_INTSTAT);
            uint32_t ep0_out      = lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000);
            uint32_t ep0_in_diag  = lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008);
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x EP0OUT=0x%x EP0IN=0x%x transfers=%d\n",
                    poll_count, diag_cmd, diag_int, ep0_out, ep0_in_diag, transfers_handled);
        }

        // mcu_sleep removed from poll loop: at 25ns/iter it costs ~3-4us
        // between consecutive polls, which exceeds the host VIP IN-retry
        // budget after a SETUP ACK. Busy-poll keeps SETUP detection within
        // 1 us of the EP0OUT interrupt.
    }

    // Report final state
    reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT final = 0x%x\n", reg_data);
    reg_data = lsu_read_32(SOC_USBHSD_INFO);
    VPRINTF(LOW, "MCU: USB INFO final = 0x%x\n", reg_data);
    VPRINTF(LOW, "MCU: USB init test - transfers handled: %d\n", transfers_handled);

    VPRINTF(LOW, "MCU: USB init test - halting\n");
    csr_write_mpmc_halt();
}
