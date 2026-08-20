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

// Description: USB HS device power-down test firmware. Boots HS device,
// handles EP0 enumeration (GET_DESCRIPTOR / SET_ADDRESS / SET_CONFIGURATION),
// then polls DEVCMDSTAT for two DCON_C events:
//   event 1 = VBUS removed (power-down)
//   event 2 = VBUS restored (power-up / reconnect)
// Prints "USB HS device powerdown PASSED" after both events are observed.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Each poll iteration is ~51 ns at MCU clock rate.
// Budget: enumeration (~2 ms) + powerdown hold (~5 us) + HS re-chirp (~300 us)
// + powerup re-enumeration wait (~2 ms) + margin = ~10 ms => 200000 iters.
#define USB_POLL_TIMEOUT 200000

// Number of DCON_C events expected: 1 for power-down, 1 for power-up.
#define DCON_EVENTS_TARGET 2

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
    uint32_t events = 0;

    VPRINTF(LOW, "MCU: hs_dev_powerdown test\n");
    boot_mcu();
    boot_usb_core();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {
        // Read DEVCMDSTAT and INTSTAT BEFORE calling usb_handle_bus_reset().
        // usb_handle_bus_reset() may issue W1C writes to DEVCMDSTAT which
        // would clear DCON_C before the check below, causing missed events.
        reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
        intstat  = lsu_read_32(SOC_USBHSD_INTSTAT);

        // Service EP0 OUT (including SETUP packets) so enumeration can complete.
        if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK)
                usb_handle_control_transfer();
        }
        if (intstat & USBHSD_INTSTAT_EP0IN_MASK)
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);

        // Handle device-level change events (bus reset, connect/disconnect).
        // Call after sampling reg_data so DCON_C is already captured above.
        if (intstat & USBHSD_INTSTAT_DEV_INT_MASK) {
            usb_handle_bus_reset();
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_DEV_INT_MASK);
        }

        // Detect DCON_C (device connection change). DCON_C is a sticky W1C bit
        // in DEVCMDSTAT; it is set when VBUS is removed or applied.
        // reg_data was sampled before any W1C writes so DCON_C is reliable here.
        if (reg_data & USBHSD_DEVCMDSTAT_DCON_C_MASK) {
            // Clear DCON_C (W1C).
            lsu_write_32(SOC_USBHSD_DEVCMDSTAT,
                lsu_read_32(SOC_USBHSD_DEVCMDSTAT) | USBHSD_DEVCMDSTAT_DCON_C_MASK);
            events++;
            VPRINTF(LOW, "MCU: DCON_C event %d DEVCMDSTAT=0x%x\n", events, reg_data);
            if (events >= DCON_EVENTS_TARGET) {
                VPRINTF(LOW, "USB HS device powerdown PASSED\r\n");
                break;
            }
        }
    }

    if (events < DCON_EVENTS_TARGET)
        VPRINTF(LOW, "MCU: hs_dev_powerdown TIMEOUT events=%d\n", events);

    VPRINTF(LOW, "MCU: hs_dev_powerdown test complete\n");
    csr_write_mpmc_halt();
}
