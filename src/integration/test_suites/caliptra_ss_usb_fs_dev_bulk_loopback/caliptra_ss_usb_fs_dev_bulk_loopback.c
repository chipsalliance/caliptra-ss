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
#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

#define USB_POLL_TIMEOUT 50000

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
    uint32_t ep1out_entry;
    uint32_t ep1in_entry;
    uint32_t rx_word;
    uint32_t i;
    uint32_t dma_base;
    int      loopback_done;

    boot_mcu();
    boot_usb_core();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    dma_base      = USB_DMA_BASE_ADDR;
    loopback_done = 0;

    /* Arm EP1 OUT to receive 64 bytes into SRAM at offset 0x200 */
    ep1out_entry = USB_EP_ENTRY_ACTIVE | USB_EP_ENTRY_NBYTES(64) | USB_EP_ENTRY_ADDR(0x200);
    lsu_write_32(dma_base + 0x010, ep1out_entry);

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {
        usb_handle_bus_reset();
        reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
        intstat  = lsu_read_32(SOC_USBHSD_INTSTAT);

        if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK)
                usb_handle_control_transfer();
        }
        if (intstat & USBHSD_INTSTAT_EP0IN_MASK)
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);

        if (!loopback_done && (intstat & USBHSD_INTSTAT_EP1OUT_MASK)) {
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP1OUT_MASK);
            /* Copy received data from EP1 OUT buffer to EP1 IN buffer */
            for (i = 0; i < 64; i += 4) {
                rx_word = lsu_read_32(dma_base + 0x200 + i);
                lsu_write_32(dma_base + 0x240 + i, rx_word);
            }
            /* Arm EP1 IN to send the loopback data */
            ep1in_entry = USB_EP_ENTRY_ACTIVE | USB_EP_ENTRY_NBYTES(64) | USB_EP_ENTRY_ADDR(0x240);
            lsu_write_32(dma_base + 0x018, ep1in_entry);
            loopback_done = 1;
        }

        if (loopback_done && !(lsu_read_32(dma_base + 0x018) & USB_EP_ENTRY_ACTIVE)) {
            /* EP1 IN transfer completed */
            VPRINTF(LOW, "USB FS dev bulk loopback PASSED\r\n");
            break;
        }
    }

    csr_write_mpmc_halt();
}
