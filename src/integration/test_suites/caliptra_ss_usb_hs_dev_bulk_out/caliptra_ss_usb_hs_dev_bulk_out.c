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
// Description: USB HS device bulk OUT test firmware for the Caliptra SS.
//
//
//
// This firmware:
//   - Boots MCU and USB core in HS device mode
//   - Handles enumeration (bus reset + EP0 SETUP packets)
//   - Arms EP1 OUT (4096-byte buffer) after SET_CONFIGURATION
//   - Verifies received data: word[i] == i for i = 0..1023

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

#define USB_POLL_TIMEOUT              4000
// EP1 OUT buffer placed after EP0 buffers in USB SRAM (EP0 uses 0x000-0x1FF).
#define USB_SRAM_EP1_OUT_BUF_OFFSET   0x200u
// 2048 bytes = 512 x 4-byte words (HS bulk, 4 x 512-byte packets).
// Capped at 2048 B so the EP1 OUT buffer (at SRAM offset 0x200) fits
// within the 4096-byte USB SRAM (0x200..0x9FF).
#define USB_HS_BULK_TRANSFER_BYTES    2048u
#define USB_EP_LIST_EP1_OUT_OFFSET    0x010u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

static void usb_ep1_out_arm(void) {
    // Use USB_EP_ENTRY_ABS_ADDR so the DMA engine reconstructs the correct
    // absolute AXI buffer address. DATABUFSTART only contributes bits[31:22],
    // so addr_offset must be bits[16:6] of the absolute AXI address:
    //   (USB_DEV0_DMA_BASE_ADDR + USB_SRAM_EP1_OUT_BUF_OFFSET)
    //   = 0x20001100 + 0x200 = 0x20001300
    //   addr_offset = 0x20001300 >> 6 & 0x7FF = 0x4C
    uint32_t ep1_out = USB_EP_ENTRY_ACTIVE
                     | USB_EP_ENTRY_NBYTES(USB_HS_BULK_TRANSFER_BYTES)
                     | USB_EP_ENTRY_ABS_ADDR(USB_DEV0_DMA_BASE_ADDR + USB_SRAM_EP1_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET, ep1_out);
    VPRINTF(LOW, "MCU: EP1 OUT armed for %d bytes\n", USB_HS_BULK_TRANSFER_BYTES);
}

static uint32_t usb_ep1_out_read(void) {
    return lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET);
}

void main(void) {
    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t transfers_handled = 0;
    bool     ep1_armed         = false;
    bool     bulk_done         = false;

    VPRINTF(LOW, "=================\nMCU: USB HS device bulk OUT test\n=================\n\n");

    boot_mcu();
    boot_usb_core();
    // usb_hub_init_and_connect() (called inside boot_usb_core()) has already
    // programmed the HUB RAM and set HUB_EN. USBDC0's own EP list/DEVCMDSTAT/
    // DCON are also now fully programmed (end of boot_usb_core()), so it is
    // safe to connect the hub upstream: usb_hub_connect() sets HUB_CONNECT,
    // per the reference janus_hub_ctrl_bfm.sv two-phase sequencing. Only
    // after this call will the host see the hub on the bus and begin
    // enumerating its downstream port 0 (USBDC0).
    usb_hub_connect();
    mcu_cptra_advance_brkpoint();

    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {


        usb_handle_bus_reset();
        reg_data = lsu_read_32(USB_DEV0_INTSTAT);

        if (reg_data & USBHSD_INTSTAT_DEV_INT_MASK) {
            uint32_t cmd = lsu_read_32(USB_DEV0_DEVCMDSTAT);
            if (cmd & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
                if (ep1_armed) {
                    ep1_armed = false;
                    VPRINTF(LOW, "MCU: Bus reset - EP1 arm cleared\n");
                }
            }
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_DEV_INT_MASK);
        }

        if (reg_data & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            uint32_t cmd = lsu_read_32(USB_DEV0_DEVCMDSTAT);
            if (cmd & USBHSD_DEVCMDSTAT_SETUP_MASK) {
                // SETUP packet received - decode and respond.
                usb_handle_control_transfer();
                transfers_handled++;
                if (!ep1_armed) {
                    usb_ep1_out_arm();
                    ep1_armed = true;
                }
            } else {
                // Status-stage ZLP OUT for a control-read completed.
                // HW cleared ACTIVE on the EP0 OUT descriptor; re-arm it
                // so the next SETUP packet is received instead of NAK'd.
                // Matches janus_ahb_fw_bfm.sv: dma_write32(EP0_OUT_DESC, 0xa0000000).
                usb_ep0_arm_out();
            }
        }

        if (reg_data & USBHSD_INTSTAT_EP0IN_MASK) {
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);
        }

        // EP1 OUT completion: use INTSTAT EP1OUT bit rather than polling the
        // EP list ACTIVE bit directly. The EP1OUT interrupt is set by hardware
        // only after the USB DMA engine has fully committed all data and the
        // packet handshake is complete. Polling ACTIVE alone can race against
        // the final DMA write, causing a single-byte corruption on the last
        // 512-byte packet when the VIP performs a retry.
        if (ep1_armed && (reg_data & USBHSD_INTSTAT_EP1OUT_MASK)) {
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP1OUT_MASK);

            uint32_t ep1_entry = usb_ep1_out_read();
            uint32_t residual  = (ep1_entry >> 11) & 0x7FFFu;
            uint32_t received  = USB_HS_BULK_TRANSFER_BYTES - residual;
            VPRINTF(LOW, "MCU: EP1 OUT complete - received %d bytes\n", received);

            // Verify COUNT pattern: word[i] == i
            uint32_t errors = 0;
            for (uint32_t i = 0; i < USB_HS_BULK_TRANSFER_BYTES; i += 4) {
                uint32_t actual   = lsu_read_32(USB_DMA_BASE_ADDR
                                                + USB_SRAM_EP1_OUT_BUF_OFFSET + i);
                uint32_t expected = i / 4u;
                if (actual != expected) {
                    VPRINTF(LOW,
                        "MCU: MISMATCH at offset 0x%x: got 0x%x expected 0x%x\n",
                        i, actual, expected);
                    errors++;
                }
            }

            if (errors == 0)
                VPRINTF(LOW, "MCU: USB HS dev bulk OUT - data check PASSED\n");
            else
                VPRINTF(LOW, "MCU: USB HS dev bulk OUT - data check FAILED (%d errors)\n",
                        errors);

            bulk_done = true;
            VPRINTF(LOW, "MCU: bulk OUT complete - remaining in USB event loop to"
                    " keep servicing EP0/DEV interrupts (host may still issue"
                    " post-bulk control transfers / suspend sequencing before"
                    " halting, matching reference janus_ahb_fw_bfm.sv's"
                    " never-exiting service_irq() loop)\n");
        }

        if (poll_count % 2000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x ep1_armed=%d\n",
                    poll_count,
                    lsu_read_32(USB_DEV0_DEVCMDSTAT),
                    lsu_read_32(USB_DEV0_INTSTAT),
                    (int)ep1_armed);

        }
    }

    if (!bulk_done)
        VPRINTF(LOW, "MCU: USB HS device bulk OUT - TIMEOUT\n");

    VPRINTF(LOW, "MCU: USB HS device bulk OUT test - halting\n");
    csr_write_mpmc_halt();
}
