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
// Description: USB HS device NBytes field test firmware for the Caliptra SS.
//
// Verifies the NBytes residual = 0 (all bytes received) and byte pattern.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

#define USB_POLL_TIMEOUT             30000
#define USB_SRAM_EP1_OUT_BUF_OFFSET  0x200u
#define USB_HS_NBYTE_BYTES           512u
#define USB_EP_LIST_EP1_OUT_OFFSET   0x010u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

static void usb_ep1_out_arm(void) {
    uint32_t ep1_out = USB_EP_ENTRY_ACTIVE
                     | USB_EP_ENTRY_NBYTES(USB_HS_NBYTE_BYTES)
                     | USB_EP_ENTRY_ADDR(USB_SRAM_EP1_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET, ep1_out);
}

void main(void) {
    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t intstat;
    uint32_t entry;
    uint32_t residual;
    bool     ep1_armed = false;
    bool     done      = false;

    VPRINTF(LOW, "=================\nMCU: USB HS device nbyte test\n=================\n\n");

    boot_mcu();
    boot_usb_core();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT && !done; poll_count++) {
        usb_handle_bus_reset();
        reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
        intstat  = lsu_read_32(SOC_USBHSD_INTSTAT);

        if (intstat & USBHSD_INTSTAT_DEV_INT_MASK) {
            if (reg_data & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
                ep1_armed = false;
            }
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_DEV_INT_MASK);
        }

        if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();
                if (!ep1_armed) { usb_ep1_out_arm(); ep1_armed = true; }
            }
        }
        if (intstat & USBHSD_INTSTAT_EP0IN_MASK)
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);

        if (ep1_armed) {
            entry    = lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET);
            if (!(entry & USB_EP_ENTRY_ACTIVE)) {
                residual = (entry >> 11) & 0x7FFFu;
                VPRINTF(LOW, "MCU: EP1 done, residual=%d (expect 0)\n", residual);
                if (residual == 0)
                    VPRINTF(LOW, "MCU: USB HS nbyte test PASSED\n");
                else
                    VPRINTF(LOW, "MCU: USB HS nbyte test FAILED - unexpected residual\n");
                done = true;
            }
        }
    }

    if (!done) VPRINTF(LOW, "MCU: USB HS nbyte test TIMEOUT\n");
    csr_write_mpmc_halt();
}
