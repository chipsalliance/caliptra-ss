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
// Including mcu_isr.h is what makes the build system compile and link
// mcu_isr.o for this test (see tools/scripts/Makefile).
#include "mcu_isr.h"

// Poll loop ceiling. Must outlast the host-side enumeration start: with the
// interrupt-driven loop each iteration is only a few DCCM accesses, so 4000
// iterations expired at ~505 us while the host does not issue its first SETUP
// until ~690 us. The loop then never saw a SETUP, NAK'd the host and reported
// TIMEOUT. Sized to match the ISO test (100000) so the ceiling is only reached
// when the DUT genuinely never completes the transfer.
#define USB_POLL_TIMEOUT              100000

// EP1 OUT buffer placed after EP0 buffers in USB SRAM (EP0 uses 0x000-0x1FF).
#define USB_SRAM_EP1_OUT_BUF_OFFSET   0x200u
// 1024 bytes = 256 x 4-byte words (FS bulk, 16 x 64-byte packets).
// Must match USB_FS_DEV_BULK_WORDS in
// testbench/uvm/usb/caliptra_ss_usb_fs_dev_bulk_out_sequence.svh. The size is
// set by the host side: the VIP constraint
// reasonable_fixed_transfer_size_non_isoc_intr bounds a fixed transfer to
// (max_packet_size << 4), and at full speed EP1 bulk has a 64-byte max packet
// size, giving a 1024-byte ceiling. The earlier 2048 made the host sequence
// randomize() unsolvable. 1024 B also fits the USB SRAM window at offset 0x200.
#define USB_FS_BULK_TRANSFER_BYTES    1024u

#define USB_EP_LIST_EP1_OUT_OFFSET    0x010u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

// Storage for the symbols the ISR library declares extern.
volatile uint32_t intr_count;
volatile mcu_intr_received_s mcu_intr_rcv = {0};

#ifdef CPT_VERBOSITY

    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

static void usb_ep1_out_arm(void) {
    // Use USB_EP_ENTRY_ABS_ADDR so the DMA engine reconstructs the correct
    // absolute AXI buffer address. DATABUFSTART only contributes bits[31:22],
    // so addr_offset must be bits[16:6] of the absolute AXI address:
    //   (USB_DEV_DMA_BASE_ADDR + USB_SRAM_EP1_OUT_BUF_OFFSET)
    //   = 0x20001100 + 0x200 = 0x20001300
    //   addr_offset = 0x20001300 >> 6 & 0x7FF = 0x4C
    uint32_t ep1_out = USB_EP_ENTRY_ACTIVE
                     | USB_EP_ENTRY_NBYTES(USB_FS_BULK_TRANSFER_BYTES)
                     | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR + USB_SRAM_EP1_OUT_BUF_OFFSET);
    lsu_write_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET, ep1_out);

    // Enable the EP1 OUT interrupt. boot_usb_core_fs() only enables DEV_INT,
    // EP0OUT and EP0IN, and service_usb_intr() masks INTSTAT with INTEN, so
    // without this the EP1 OUT completion would never reach the mailbox.
    lsu_write_32(USB_DEV_INTEN,
                 lsu_read_32(USB_DEV_INTEN) | USBHSD_INTSTAT_EP1OUT_MASK);

    VPRINTF(LOW, "MCU: EP1 OUT armed for %d bytes\n", USB_FS_BULK_TRANSFER_BYTES);

}

static uint32_t usb_ep1_out_read(void) {
    return lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET);
}

void main(void) {
    uint32_t poll_count;
    uint32_t usb_events;
    uint32_t transfers_handled = 0;

    bool     ep1_armed         = false;
    bool     bulk_done         = false;

    VPRINTF(LOW, "=================\nMCU: USB HS device bulk OUT test\n=================\n\n");

    boot_mcu();
    boot_usb_core_fs();

    // Enable the USB interrupt (PIC vector 3) now that boot_usb_core_fs() has
    // programmed INTEN and cleared any stale INTSTAT bits. Deliberately not
    // init_interrupts(): that routine also writes the MCI and I3C interrupt
    // registers, and this early the I3C write does not complete, stalling the
    // LSU pipeline before mstatus.MIE is set. init_usb_interrupts() touches
    // only vector 3.
    intr_count = 0;
    init_usb_interrupts();

    // usb_hub_init_and_connect() (called inside boot_usb_core_fs()) has already

    // programmed the HUB RAM and set HUB_EN. USBDC0's own EP list/DEVCMDSTAT/
    // DCON are also now fully programmed (end of boot_usb_core_fs()), so it is
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

        // Drain the ISR mailbox. service_usb_intr() already read and
        // acknowledged INTSTAT, so the foreground loop must not touch INTSTAT
        // itself. Snapshot then clear by complement so bits the ISR sets while
        // we are handling this batch are not lost.
        usb_events = mcu_intr_rcv.usb;
        mcu_intr_rcv.usb &= ~usb_events;

        if (usb_events & USBHSD_INTSTAT_DEV_INT_MASK) {

            uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
            if (cmd & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
                if (ep1_armed) {
                    ep1_armed = false;
                    VPRINTF(LOW, "MCU: Bus reset - EP1 arm cleared\n");
                }
            }
            // No INTSTAT write here: service_usb_intr() already cleared it.
        }

        if (usb_events & USBHSD_INTSTAT_EP0OUT_MASK) {
            uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);

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

        // EP0 IN completion needs no action: the ISR already acknowledged it.


        // EP1 OUT completion: use INTSTAT EP1OUT bit rather than polling the
        // EP list ACTIVE bit directly. The EP1OUT interrupt is set by hardware
        // only after the USB DMA engine has fully committed all data and the
        // packet handshake is complete. Polling ACTIVE alone can race against
        // the final DMA write, causing a single-byte corruption on the last
        // 512-byte packet when the VIP performs a retry.
        if (ep1_armed && (usb_events & USBHSD_INTSTAT_EP1OUT_MASK)) {


            uint32_t ep1_entry = usb_ep1_out_read();
            uint32_t residual  = (ep1_entry >> 11) & 0x7FFFu;
            uint32_t received  = USB_FS_BULK_TRANSFER_BYTES - residual;
            VPRINTF(LOW, "MCU: EP1 OUT complete - received %d bytes\n", received);

            // Verify COUNT pattern: word[i] == i
            uint32_t errors = 0;
            for (uint32_t i = 0; i < USB_FS_BULK_TRANSFER_BYTES; i += 4) {
                uint32_t actual   = lsu_read_32(USB_DEV_DMA_BASE_ADDR
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

        if (poll_count % 10000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x ep1_armed=%d intr_cnt=%d\n",
                    poll_count,
                    lsu_read_32(USB_DEV_DEVCMDSTAT),
                    lsu_read_32(USB_DEV_INTSTAT),
                    (int)ep1_armed,
                    intr_count);

        }
    }

    if (!bulk_done)
        VPRINTF(LOW, "MCU: USB HS device bulk OUT - TIMEOUT\n");

    VPRINTF(LOW, "MCU: USB HS device bulk OUT test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
