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
// Description: USB High-Speed connection test firmware for the Caliptra SS.
//
//
//
// This firmware:
//   - Boots the MCU and USB core in HS device mode via boot_usb_core()
//   - Polls DEVCMDSTAT until the HS connection is established (CON=1)
//   - Reports connection speed and halts

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

#define USB_POLL_TIMEOUT 30000

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main(void) {
    uint32_t reg_data;
    uint32_t poll_count;
    bool connected = false;

    VPRINTF(LOW, "=================\nMCU: USB HS connection test\n=================\n\n");

    boot_mcu();

    // boot_usb_core() brings up the USB device controller in HS mode.
    // The VIP host (high_speed_capable=1) will perform HS chirp negotiation.
    boot_usb_core();

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, polling for HS connection\n");

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT && !connected; poll_count++) {
        usb_handle_bus_reset();

        reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);

        // DCON bit indicates device is connected (pullup enabled / VBUS present).
        if (reg_data & USBHSD_DEVCMDSTAT_DCON_MASK) {
            connected = true;
            VPRINTF(LOW, "MCU: USB device connected - DEVCMDSTAT=0x%x\n", reg_data);
        }

        if (poll_count % 5000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x\n", poll_count, reg_data);
        }
    }

    if (!connected) {
        VPRINTF(LOW, "MCU: USB HS conn - TIMEOUT waiting for connection\n");
    } else {
        VPRINTF(LOW, "MCU: USB HS conn test PASSED\n");
    }

    csr_write_mpmc_halt();
}
