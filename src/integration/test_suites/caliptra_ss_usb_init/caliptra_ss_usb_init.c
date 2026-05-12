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
//********************************************************************************
// Description: USB device controller initialization test for Caliptra Subsystem
//
//  Boots the MCU, initializes USB device controller (EP list, SRAM buffers,
//  DEVCMDSTAT), then brings up Caliptra core. Polls for SETUP packets from
//  the UVM VIP host and handles GET_DESCRIPTOR / SET_ADDRESS requests.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "string.h"
#include "stdint.h"
#include "veer-csr.h"

#define USB_POLL_TIMEOUT 10000

// USB standard request types
#define USB_REQ_GET_DESCRIPTOR  0x06
#define USB_REQ_SET_ADDRESS     0x05

// USB descriptor types
#define USB_DESC_DEVICE         0x01

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Minimal USB 2.0 device descriptor (18 bytes, packed as uint32_t for SRAM writes)
static const uint32_t dev_desc_words[] = {
    0x00020112,  // bLength=18, bDescType=1(DEVICE), bcdUSB=0x0200 (LE)
    0x40000000,  // bDevClass=0, bDevSubClass=0, bDevProto=0, bMaxPktSz0=64
    0x00000000,  // idVendor=0x0000, idProduct=0x0000
    0x00000100,  // bcdDevice=0x0100, iManufacturer=0
    0x01000000   // iProduct=0, iSerialNumber=0, bNumConfigurations=1
};


void main (void) {

    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t setup_word0, setup_word1;
    uint8_t  bRequest, bmRequestType;
    uint16_t wValue, wLength;
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
        {
            uint32_t cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
            if (cmd & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
                VPRINTF(LOW, "MCU: Bus reset detected (direct DEVCMDSTAT poll)\n");
                // Clear reset change (W1C)
                lsu_write_32(SOC_USBHSD_DEVCMDSTAT, cmd | USBHSD_DEVCMDSTAT_DRES_C_MASK);

                // Re-initialize EP0 after bus reset - hardware may clear Active bit
                uint32_t ep0_out_entry = (1u << 31) | (8u << 16) | (USB_SRAM_EP0_OUT_BUF_OFFSET >> 6);
                lsu_write_32(USB_DMA_BASE_ADDR + 0x000, ep0_out_entry);
                // Re-set SETUP buffer address
                lsu_write_32(USB_DMA_BASE_ADDR + 0x004, (USB_SRAM_SETUP_BUF_OFFSET >> 6));
                // Re-set EP0 IN buffer address
                lsu_write_32(USB_DMA_BASE_ADDR + 0x008, (USB_SRAM_EP0_IN_BUF_OFFSET >> 6));
                VPRINTF(LOW, "MCU: Re-initialized EP0 after bus reset (EP0OUT=0x%x)\n", ep0_out_entry);

                // Reset device address to 0 per USB spec
                cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
                cmd &= ~0x7Fu;  // Clear DEV_ADDR[6:0]
                lsu_write_32(SOC_USBHSD_DEVCMDSTAT, cmd);
            }
        }

        // Check for device-level interrupts (bus reset, connect change)
        reg_data = lsu_read_32(SOC_USBHSD_INTSTAT);
        if (reg_data & USBHSD_INTSTAT_DEV_INT_MASK) {
            uint32_t cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
            VPRINTF(LOW, "MCU: DEV_INT - DEVCMDSTAT = 0x%x\n", cmd);

            if (cmd & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
                VPRINTF(LOW, "MCU: Bus reset detected\n");
                // Clear reset change (W1C) and re-enable device
                lsu_write_32(SOC_USBHSD_DEVCMDSTAT,
                    cmd | USBHSD_DEVCMDSTAT_DRES_C_MASK);

                // Re-initialize EP0 after bus reset
                uint32_t ep0_out_entry = (1u << 31) | (8u << 16) | (USB_SRAM_EP0_OUT_BUF_OFFSET >> 6);
                lsu_write_32(USB_DMA_BASE_ADDR + 0x000, ep0_out_entry);
                lsu_write_32(USB_DMA_BASE_ADDR + 0x004, (USB_SRAM_SETUP_BUF_OFFSET >> 6));
                lsu_write_32(USB_DMA_BASE_ADDR + 0x008, (USB_SRAM_EP0_IN_BUF_OFFSET >> 6));
                VPRINTF(LOW, "MCU: Re-initialized EP0 after bus reset (DEV_INT path)\n");
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
                VPRINTF(LOW, "MCU: SETUP packet received\n");

                // Read 8-byte SETUP data from SRAM via DMA port
                setup_word0 = lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_SETUP_BUF_OFFSET);
                setup_word1 = lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_SETUP_BUF_OFFSET + 4);
                VPRINTF(LOW, "MCU: SETUP[0]=0x%x SETUP[1]=0x%x\n", setup_word0, setup_word1);

                bmRequestType = (setup_word0 >>  0) & 0xFF;
                bRequest      = (setup_word0 >>  8) & 0xFF;
                wValue        = (setup_word0 >> 16) & 0xFFFF;
                wLength       = (setup_word1 >> 16) & 0xFFFF;

                // Clear EP0 IN interrupt before programming response
                lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);

                if (bRequest == USB_REQ_GET_DESCRIPTOR) {
                    uint8_t desc_type = (wValue >> 8) & 0xFF;
                    VPRINTF(LOW, "MCU: GET_DESCRIPTOR type=%d len=%d\n", desc_type, wLength);

                    if (desc_type == USB_DESC_DEVICE) {
                        // Write device descriptor to EP0 IN buffer in SRAM
                        uint32_t nbytes = (wLength < 18) ? wLength : 18;
                        for (uint32_t i = 0; i < 5; i++) {
                            lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP0_IN_BUF_OFFSET + (i * 4),
                                         dev_desc_words[i]);
                        }

                        // Update EP0 IN entry: Active=1, NBytes, addr_offset
                        uint32_t ep0_in = (1u << 31)
                                        | (nbytes << 16)
                                        | (USB_SRAM_EP0_IN_BUF_OFFSET >> 6);
                        lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x08, ep0_in);
                        VPRINTF(LOW, "MCU: EP0 IN entry = 0x%x\n", ep0_in);

                        // EP0 OUT for status phase: Active=1, NBytes=0
                        uint32_t ep0_out = (1u << 31)
                                         | (0u << 16)
                                         | (USB_SRAM_EP0_OUT_BUF_OFFSET >> 6);
                        lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x00, ep0_out);

                        // Set IntOnNAK_CO for status phase detection
                        cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
                        cmd |= USBHSD_DEVCMDSTAT_INTONNAK_CO_MASK;
                        cmd &= ~USBHSD_DEVCMDSTAT_INTONNAK_CI_MASK;
                        lsu_write_32(SOC_USBHSD_DEVCMDSTAT, cmd);
                    }
                } else if (bRequest == USB_REQ_SET_ADDRESS) {
                    uint8_t new_addr = wValue & 0x7F;
                    VPRINTF(LOW, "MCU: SET_ADDRESS addr=%d\n", new_addr);

                    // Status phase: EP0 IN sends ZLP
                    uint32_t ep0_in = (1u << 31)
                                    | (0u << 16)
                                    | (USB_SRAM_EP0_IN_BUF_OFFSET >> 6);
                    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x08, ep0_in);

                    // EP0 OUT: Active=1, NBytes=0
                    uint32_t ep0_out = (1u << 31)
                                     | (0u << 16)
                                     | (USB_SRAM_EP0_OUT_BUF_OFFSET >> 6);
                    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x00, ep0_out);

                    // Update device address in DEVCMDSTAT
                    cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
                    cmd = (cmd & ~USBHSD_DEVCMDSTAT_DEV_ADDR_MASK) | new_addr;
                    lsu_write_32(SOC_USBHSD_DEVCMDSTAT, cmd);
                } else {
                    VPRINTF(LOW, "MCU: Unhandled request 0x%x - stalling\n", bRequest);
                }

                // Clear SETUP bit LAST (per Integration Guide §4.2.4.1.1)
                cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
                lsu_write_32(SOC_USBHSD_DEVCMDSTAT, cmd | USBHSD_DEVCMDSTAT_SETUP_MASK);

                // Verify SETUP cleared and EP0 IN is active
                cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
                uint32_t ep0_in_rb = lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x08);
                VPRINTF(LOW, "MCU: Post-SETUP-clear DEVCMDSTAT=0x%x EP0IN=0x%x\n", cmd, ep0_in_rb);

                transfers_handled++;
                VPRINTF(LOW, "MCU: Transfers handled = %d\n", transfers_handled);
            }
        }

        // Periodic diagnostic dump
        if (poll_count % 1000 == 0 && poll_count > 0) {
            uint32_t diag_cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
            uint32_t diag_int = lsu_read_32(SOC_USBHSD_INTSTAT);
            uint32_t ep0_out = lsu_read_32(USB_DMA_BASE_ADDR + 0x000);
            uint32_t ep0_in_diag = lsu_read_32(USB_DMA_BASE_ADDR + 0x008);
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x EP0OUT=0x%x EP0IN=0x%x\n",
                    poll_count, diag_cmd, diag_int, ep0_out, ep0_in_diag);
        }

        mcu_sleep(10);
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
