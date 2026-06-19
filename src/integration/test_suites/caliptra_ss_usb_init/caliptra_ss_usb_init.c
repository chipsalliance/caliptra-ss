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
#define USB_EVENT_LOOP_DIAG_PERIOD 1000u
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

    VPRINTF(LOW, "=================\nMCU: USB init test\n=================\n\n");

    // Standard MCU boot sequence
    boot_mcu();

    // Initialize USB device controller BEFORE Caliptra bringup.
    // USB PHY and pull-up need time to settle while Caliptra boots.
    // No application descriptor/class hooks: use the built-in USB defaults.
    boot_usb_core(0, 0);

    // Caliptra core bringup
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra core ready, entering USB event loop\n");

    usb_dump_state("initial");

    // --- Main USB event loop: poll for SETUP packets ---
    usb_event_loop(USB_POLL_TIMEOUT);

    // Report final state
    usb_dump_state("final");
    reg_data = lsu_read_32(SOC_USBHSD_INFO);
    VPRINTF(LOW, "MCU: USB INFO final = 0x%x\n", reg_data);

    VPRINTF(LOW, "MCU: USB init test - halting\n");
    csr_write_mpmc_halt();
}
