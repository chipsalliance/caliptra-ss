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
// Description: USB GET_INTERFACE test for Caliptra Subsystem (Full Speed)
//
//  Full-speed counterpart of caliptra_ss_usb_hs_dev_get_interface.c. Boots the
//  MCU, brings up the USB hub-composite IP in FS-only mode via
//  boot_usb_core_fs() (which sets DEVCMDSTAT.PFSC to suppress the device-side
//  K-chirp so the link stays at full speed for the FS-only host VIP), connects
//  the hub upstream and then runs the EP0 event loop so the VIP host can
//  enumerate the hub and USBDC0.
//
//  Two targets are exercised. The hub answers GET_INTERFACE entirely in EP0
//  hardware (SETUP-match ROM entry 0x00000A81, one data byte = selected
//  bAlternateSetting). USBDC0 answers from the shared EP0 dispatcher in
//  libs/usb/usb.c, which this event loop invokes through
//  usb_handle_control_transfer(), so no test-specific firmware logic is
//  required. Both response values are checked host-side by
//  caliptra_ss_usb_data_check_api.
//
//  This is a pure polling test with no ISR involvement (no mcu_isr.h, no
//  init_usb_interrupts(), no ISR mailbox), matching the other FS
//  command-value-check tests: each iteration reads INTSTAT and
//  write-1-to-clears every serviced bit (DEV_INT, EP0OUT, EP0IN). The poll
//  budget is 4x the HS variant because an FS frame is 1 ms versus the 125 us
//  HS microframe, so enumeration plus the two control reads take proportionally
//  longer in bus time.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

#define USB_POLL_TIMEOUT 8000

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main(void) {
    uint32_t reg_data;
    uint32_t intstat;
    uint32_t poll_count;
    uint32_t transfers_handled = 0;

    VPRINTF(LOW, "=================\nMCU: USB FS get_interface test\n=================\n\n");

    boot_mcu();

    // FS-only bring-up of the hub-composite IP. Also programs and validates
    // the HUB RAM and sets HUB_EN (via usb_hub_init_and_connect()).
    boot_usb_core_fs();

    // Two-phase hub bring-up: HUB_EN was set inside boot_usb_core_fs(); now
    // that USBDC0's EP list / DEVCMDSTAT / DCON are fully programmed it is
    // safe to set HUB_CONNECT so the host sees the hub on the bus.
    usb_hub_connect();

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT = 0x%x\n", reg_data);
    reg_data = lsu_read_32(USB_DEV_INTSTAT);
    VPRINTF(LOW, "MCU: USB INTSTAT = 0x%x\n", reg_data);

    // --- Main USB event loop: poll INTSTAT for USB events ---
    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {

        // Direct DEVCMDSTAT poll for bus reset (fallback path; DEV_INT is
        // also cleared below when observed in INTSTAT).
        usb_handle_bus_reset();

        reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
        intstat  = lsu_read_32(USB_DEV_INTSTAT);

        // Device-level interrupt (bus reset / connect change). W1C DEV_INT so
        // it does not remain asserted on the hardware IRQ line.
        if (intstat & DEV0_CSR_INTSTAT_DEV_INT_MASK) {
            if (reg_data & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
            }
            lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_DEV_INT_MASK);
        }

        // EP0 OUT interrupt (SETUP or status-stage OUT). W1C EP0OUT first,
        // then service the SETUP packet if DEVCMDSTAT.SETUP is set. Do not
        // VPRINTF before usb_handle_control_transfer(): each VPRINTF adds
        // ~1-2us and the host VIP gives up on IN polling shortly after the
        // SETUP ACK. Logging happens inside the handler.
        if (intstat & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0OUT_MASK);
            if (reg_data & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
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
        if (intstat & DEV0_CSR_INTSTAT_EP0IN_MASK) {
            lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);
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

    VPRINTF(LOW, "MCU: USB FS get_interface test - transfers handled: %d\n", transfers_handled);

    VPRINTF(LOW, "MCU: USB FS get_interface test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
