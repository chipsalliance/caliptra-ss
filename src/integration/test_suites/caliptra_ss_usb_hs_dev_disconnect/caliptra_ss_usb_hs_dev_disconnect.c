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
// Description: USB HS device disconnect/reconnect test firmware for Caliptra SS.
//
//
// Firmware monitors DEVCMDSTAT for DCON_C (connect change) events that signal
// the VIP host disconnecting and reconnecting. On reconnect, verifies the
// HS link is re-established by checking SPEED field = 10 (HS).

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

#define USB_POLL_TIMEOUT  50000

// DEVCMDSTAT SPEED field values: 00=FS, 10=HS (bits [23:22]).
#define USBHSD_SPEED_HS   (0x2u << 22)

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main(void) {
    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t intstat;
    uint32_t speed;
    uint32_t disconnect_seen = 0;
    bool     reconnected     = false;

    VPRINTF(LOW, "=================\nMCU: USB HS device disconnect test\n=================\n\n");

    boot_mcu();
    boot_usb_core();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, waiting for initial HS connection\n");

    // Wait for initial HS connection (DCON=1).
    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {
        reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
        if (reg_data & USBHSD_DEVCMDSTAT_DCON_MASK) {
            VPRINTF(LOW, "MCU: Initial connection detected - DEVCMDSTAT=0x%x\n", reg_data);
            break;
        }
    }

    // Main event loop - watch for disconnect then reconnect.
    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT && !reconnected; poll_count++) {

        usb_handle_bus_reset();
        reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);

        // DCON_C: connect change event (disconnect or reconnect).
        if (reg_data & USBHSD_DEVCMDSTAT_DCON_C_MASK) {
            lsu_write_32(SOC_USBHSD_DEVCMDSTAT,
                         lsu_read_32(SOC_USBHSD_DEVCMDSTAT) | USBHSD_DEVCMDSTAT_DCON_C_MASK);

            if (!(reg_data & USBHSD_DEVCMDSTAT_DCON_MASK)) {
                // DCON went low - disconnect event.
                disconnect_seen++;
                VPRINTF(LOW, "MCU: Disconnect event #%d detected\n", disconnect_seen);
            } else {
                // DCON is now high again - reconnect event.
                speed = (reg_data & USBHSD_DEVCMDSTAT_SPEED_MASK);
                VPRINTF(LOW, "MCU: Reconnect detected - DEVCMDSTAT=0x%x speed_field=0x%x\n",
                        reg_data, speed >> 22);
                if (disconnect_seen > 0) {
                    reconnected = true;
                }
            }
        }

        // Also handle EP0 SETUP packets during normal operation.
        intstat = lsu_read_32(SOC_USBHSD_INTSTAT);
        if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK)
                usb_handle_control_transfer();
        }
        if (intstat & USBHSD_INTSTAT_EP0IN_MASK)
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);

        if (poll_count % 5000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x disc_seen=%d\n",
                    poll_count, reg_data, disconnect_seen);
        }
    }

    if (reconnected)
        VPRINTF(LOW, "MCU: USB HS disconnect test PASSED - reconnect verified\n");
    else
        VPRINTF(LOW, "MCU: USB HS disconnect test FAILED - no reconnect observed\n");

    csr_write_mpmc_halt();
}
