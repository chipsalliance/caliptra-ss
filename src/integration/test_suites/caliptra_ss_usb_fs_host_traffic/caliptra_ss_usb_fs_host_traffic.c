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
// Description: USB Full-Speed host traffic test firmware for the Caliptra Subsystem.
//
// Caliptra MCU firmware environment.
//
// transactor on the host side to:
//   - Set device address to 1 (DEVADDR register)
//   - Configure EP list at 0x00020000 (ENDPOINTLISTADDRESS)
//   - Enable EP1 OUT (ENDPOINTCTRL1 = 0x00880088)
//   - Prime EP1 OUT dTD (ENDPTPRIME bit 1)
//   - Wait for USBINT (IOC) after 256 bytes received
//   - Verify: data_val2 starts at 0xFF, increments before compare
//     => word[k] = 0x100 + k for k=0..63
//
// This firmware handles the USB device controller side (USB HS
// device controller) in the Caliptra SS environment:
//   - Boots MCU, brings up USB device controller in FS mode
//   - Handles bus reset and enumeration control transfers via usb driver lib
//   - Arms EP1 OUT after SET_CONFIGURATION to receive the bulk data
//   - Polls EP1 OUT for transfer completion (Active bit clears)
//   - Verifies the 256-byte data pattern matching the original mem.txt:
//     word[k] = 0x00000100 + k for k = 0..63

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Number of main poll iterations before giving up waiting for traffic.
#define USB_POLL_TIMEOUT    30000

// Bulk OUT buffer placed immediately after EP0 buffers in the USB SRAM.
// EP0 occupies 0x000-0x1FF; EP1 OUT starts at 0x200.
// Buffer size: 256 bytes (0x100) - matches original OUT_BUF at 0x30000 (256B).
#define USB_SRAM_EP1_OUT_BUF_OFFSET  0x200u
#define USB_BULK_TRANSFER_BYTES      256u

// EP1 OUT command/status list entry is at word offset 4 in the EP list
// (EP0 uses words 0-3; EP1 OUT uses word 4, offset 0x010).
// Original: ENDPOINTLISTADDRESS = 0x00020000, EP1 OUT dQH at offset 0x40.
#define USB_EP_LIST_EP1_OUT_OFFSET   0x010u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Arm EP1 OUT to receive USB_BULK_TRANSFER_BYTES bytes into the EP1 OUT SRAM
// buffer. Sets Active=1 so the hardware DMA will accept an OUT token.
// Equivalent to original: dTD Status=0x80 (Active), TotalBytesToTransfer=0x00FF.
static void usb_ep1_out_arm(void) {
    uint32_t ep1_out = USB_EP_ENTRY_ACTIVE
                     | USB_EP_ENTRY_NBYTES(USB_BULK_TRANSFER_BYTES)
                     | USB_EP_ENTRY_ADDR(USB_SRAM_EP1_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET, ep1_out);
    VPRINTF(LOW, "MCU: EP1 OUT armed (0x%x)\n", ep1_out);
}

// Read back the EP1 OUT command/status entry.
// When Active=0 the hardware has completed the DMA transfer and
// NBytes reflects the residual count.
// Original: polled via @ (posedge usb_interrupt) - USBINT IOC.
static uint32_t usb_ep1_out_read(void) {
    return lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET);
}

void main (void) {

    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t transfers_handled = 0;
    bool     ep1_armed         = false;
    bool     bulk_done         = false;

    VPRINTF(LOW, "=================\nMCU: USB FS host traffic test\n=================\n\n");

    // Standard MCU boot sequence.
    boot_mcu();

    // Bring the USB device controller up in full-speed mode.
    // The VIP host configuration sets high_speed_capable=0 so no HS chirp
    // is issued, replicating the original PORTSC1_PFSC (force FS) behavior.
    boot_usb_core();

    // Caliptra core bringup.
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra core ready, entering USB event loop\n");

    reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT = 0x%x\n", reg_data);

    // --- Main USB event loop ---
    // Handles bus resets, enumeration control transfers (equivalent to
    // original direct register writes), and
    // bulk OUT traffic detection.
    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT && !bulk_done; poll_count++) {

        // Handle bus reset (clears device address, re-arms EP0).
        usb_handle_bus_reset();

        // Read interrupt status.
        reg_data = lsu_read_32(SOC_USBHSD_INTSTAT);

        // DEV_INT: bus-level events (reset, connect change).
        if (reg_data & USBHSD_INTSTAT_DEV_INT_MASK) {
            uint32_t cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
            if (cmd & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
                // Clear EP1 arm state on bus reset.
                if (ep1_armed) {
                    ep1_armed = false;
                    VPRINTF(LOW, "MCU: Bus reset - EP1 arm cleared\n");
                }
            }
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_DEV_INT_MASK);
        }

        // EP0 OUT interrupt: SETUP or status-phase OUT.
        // Original: USBINT + ENDPTSTAT polling replaced by SETUP interrupt.
        if (reg_data & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            uint32_t cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
            if (cmd & USBHSD_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();
                transfers_handled++;

                // Arm EP1 OUT after the first SETUP response so it is ready
                // to receive the bulk data when the VIP host sends it after
                // SET_CONFIGURATION (equivalent to original EPPRIME write).
                if (!ep1_armed) {
                    usb_ep1_out_arm();
                    ep1_armed = true;
                }
            }
        }

        // EP0 IN interrupt: clear it.
        if (reg_data & USBHSD_INTSTAT_EP0IN_MASK) {
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);
        }

        // Poll EP1 OUT for completion (Active=0).
        // Original: @ (posedge usb_interrupt) after USBINTR_UE was enabled.
        if (ep1_armed) {
            uint32_t ep1_entry = usb_ep1_out_read();
            if (!(ep1_entry & USB_EP_ENTRY_ACTIVE)) {
                uint32_t residual = (ep1_entry >> 11) & 0x7FFFu;
                uint32_t received = USB_BULK_TRANSFER_BYTES - residual;
                VPRINTF(LOW, "MCU: EP1 OUT transfer complete - received %d bytes\n", received);

                // Verify received data pattern.
                // Original na_usb_fs_host_traffic.sv verification:
                //   data_val2 = 0xFF;
                //   for (i=0; i<0x100; i+=4) {
                //     usb_sb.DataRead(data_val, OUT_BUF_ADDR + i, WORD, COMPLETE_READ);
                //     data_val2 = data_val2 + 1;
                //     assert (data_val == data_val2)
                //   }
                // => word[k] = 0x00000100 + k  for k = 0..63
                uint32_t errors   = 0;
                uint32_t expected = 0x00000100u;
                for (uint32_t i = 0; i < USB_BULK_TRANSFER_BYTES; i += 4) {
                    uint32_t actual = lsu_read_32(USB_DMA_BASE_ADDR
                                                  + USB_SRAM_EP1_OUT_BUF_OFFSET + i);
                    if (actual != expected) {
                        VPRINTF(LOW, "MCU: DATA MISMATCH offset 0x%x: got 0x%x expected 0x%x\n",
                                i, actual, expected);
                        errors++;
                    }
                    expected++;
                }

                if (errors == 0) {
                    VPRINTF(LOW, "MCU: USB FS host traffic - data check PASSED\n");
                } else {
                    VPRINTF(LOW, "MCU: USB FS host traffic - data check FAILED (%d errors)\n",
                            errors);
                }

                bulk_done = true;
            }
        }

        // Periodic diagnostic dump every 2000 iterations.
        if (poll_count % 2000 == 0 && poll_count > 0) {
            uint32_t diag_cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
            uint32_t diag_int = lsu_read_32(SOC_USBHSD_INTSTAT);
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x transfers=%d ep1_armed=%d\n",
                    poll_count, diag_cmd, diag_int, transfers_handled, (int)ep1_armed);
        }
    }

    if (!bulk_done) {
        VPRINTF(LOW, "MCU: USB FS host traffic - TIMEOUT waiting for bulk data\n");
    }

    reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT final = 0x%x\n", reg_data);
    VPRINTF(LOW, "MCU: USB FS host traffic test - halting\n");
    csr_write_mpmc_halt();
}
