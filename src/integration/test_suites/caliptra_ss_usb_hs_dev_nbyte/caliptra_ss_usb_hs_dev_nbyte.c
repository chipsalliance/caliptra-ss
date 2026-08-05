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
// Description: USB HS device NBytes residual test firmware for the Caliptra SS
// RISC-V MCU environment.
//
// The VIP host performs 5 successive bulk OUT transfers to EP1, sending short
// packets of 1, 2, 3, 4, and 5 bytes respectively (all less than the 32-byte
// NBytes budget).  After each transfer this firmware:
//   1. Reads the EP1 OUT command/status list entry.
//   2. Checks NBytes residual == 32 - i  (hardware decremented by actual bytes).
//   3. Checks the buffer address offset advanced by exactly one 64-byte chunk.
//   4. Verifies the received byte pattern: buf[j] == j+1 for j = 0..i-1.
//   5. Checks that FRAME_INT is set in INTSTAT when EP1OUT fires.
//   6. Re-arms EP1 OUT with toggle-reset for the next iteration.
//
// EP list layout:
//   Word 0 (byte 0x000): EP0 OUT entry
//   Word 1 (byte 0x004): EP0 OUT high word (unused)
//   Word 2 (byte 0x008): EP0 IN  entry
//   Word 3 (byte 0x00C): EP0 IN  high word (unused)
//   Word 4 (byte 0x010): EP1 OUT entry  <- USB_EP_LIST_EP1_OUT_OFFSET
//
// SRAM buffer map:
//   0x000-0x13F  EP0 setup/out/in buffers  (from usb.h layout)
//   0x200-0x23F  EP1 OUT 32-byte receive buffer (USB_SRAM_EP1_OUT_BUF_OFFSET)
//
// After a short-packet transfer the hardware advances the buffer pointer in
// the EP list entry by one 64-byte aligned chunk:
//   expected addr_offset_field = (USB_SRAM_EP1_OUT_BUF_OFFSET + 64) >> 6

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Maximum poll iterations before declaring timeout.
// HS chirp takes ~3 ms sim time; poll loop body takes ~8 ns per iteration,
// so 500000 iterations = ~4 ms; add margin for 5 bulk-OUT iterations
// (5 x 130 us = 650 us) and enumeration (~200 us): 2000000 total.
#define USB_POLL_TIMEOUT             2000000

// EP1 OUT receive buffer placed right after EP0 buffers in the USB SRAM
// (Caliptra SS layout: EP0 ends at 0x1FF, EP1 starts at 0x200).
#define USB_SRAM_EP1_OUT_BUF_OFFSET  0x200u

// NBytes budget armed into the EP1 OUT entry for each iteration.
// The host sends short packets of 1..5 bytes; residual = 32 - i after
// each transfer.
#define USB_HS_NBYTE_BUDGET          32u

// Byte offset of the EP1 OUT command/status list entry inside USB SRAM.
// Word index 4 * 4 bytes = 0x010.
#define USB_EP_LIST_EP1_OUT_OFFSET   0x010u

// After a short-packet transfer the hardware advances the buffer address
// pointer by one 64-byte chunk.  The entry field holds (byte_addr >> 6),
// so the expected field value after one transfer is:
//   (USB_SRAM_EP1_OUT_BUF_OFFSET + 64) >> 6
#define USB_EP1_ADDR_OFFSET_EXPECTED  ((USB_SRAM_EP1_OUT_BUF_OFFSET + 64u) >> 6)

// Number of short-packet iterations (i = 1 .. USB_NBYTE_ITERATIONS).
#define USB_NBYTE_ITERATIONS         5

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Arm EP1 OUT to receive USB_HS_NBYTE_BUDGET bytes into the EP1 OUT SRAM
// buffer.  Sets Active=1 so the hardware DMA will accept the next OUT token.
// Arms EP1 OUT with A=1, NBytes=0x20, AddrOffset=USB_SRAM_EP1_OUT_BUF_OFFSET>>6.
static void usb_ep1_out_arm(void) {
    uint32_t entry = USB_EP_ENTRY_ACTIVE
                   | USB_EP_ENTRY_NBYTES(USB_HS_NBYTE_BUDGET)
                   | USB_EP_ENTRY_ADDR(USB_SRAM_EP1_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET, entry);
    VPRINTF(LOW, "MCU: EP1 OUT armed (entry=0x%08x)\n", entry);
}

// Re-arm EP1 OUT for the next transfer without the TR (toggle-reset) bit.
//
// The TR bit (bit 28) causes the USB HS device controller to delay
// INTSTAT.EP1OUT until the SOF reload (~125 us after DMA), which coincides
// with the next host packet (130 us inter-packet gap in the test sequence)
// and causes the MCU to read the next iteration's NBytes residual instead
// of the current one.
//
// Without TR, INTSTAT.EP1OUT fires immediately upon DMA completion, giving
// the MCU ample time (>100 us) to read the correct residual before the next
// packet arrives.  The DATA toggle alternates naturally (DATA0->DATA1->...),
// which the SVT host VIP tracks correctly via ACK/NAK handshake.
static void usb_ep1_out_rearm_toggle_reset(void) {
    uint32_t entry = USB_EP_ENTRY_ACTIVE
                   | USB_EP_ENTRY_NBYTES(USB_HS_NBYTE_BUDGET)
                   | USB_EP_ENTRY_ADDR(USB_SRAM_EP1_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET, entry);
    VPRINTF(LOW, "MCU: EP1 OUT re-armed (no TR) (entry=0x%08x)\n", entry);
}

void main(void) {
    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t intstat;
    uint32_t entry;
    uint32_t nbytes_residual;
    uint32_t addr_offset_field;
    uint32_t i;
    uint32_t j;
    uint32_t errors;
    uint8_t  byte_val;
    bool     ep1_armed      = false;
    bool     iter_done      = false;
    bool     frame_int_seen = false; // set whenever FRAME_INT is observed in the poll loop
    uint32_t iter           = 1;   // current short-packet length (1..5)

    VPRINTF(LOW, "=================\nMCU: USB HS device nbyte test\n=================\n\n");

    // Standard MCU and Caliptra core boot sequence.
    boot_mcu();
    boot_usb_core();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra core ready, entering USB nbyte event loop\n");

    // Pre-fill the EP1 OUT SRAM buffer with 0xDE so stale data is visible.
    for (i = 0; i < USB_HS_NBYTE_BUDGET; i += 4) {
        lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP1_OUT_BUF_OFFSET + i, 0xDEDEDEDEu);
    }

    // --- Main USB event loop ---
    // Runs until all USB_NBYTE_ITERATIONS short-packet transfers are verified
    // or the poll timeout is reached.
    for (poll_count = 0;
         poll_count < USB_POLL_TIMEOUT && iter <= USB_NBYTE_ITERATIONS;
         poll_count++) {

        // Handle bus reset (clears device address, re-arms EP0).
        usb_handle_bus_reset();

        reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
        intstat  = lsu_read_32(SOC_USBHSD_INTSTAT);

        // DEV_INT: bus-level events (reset, connect change).
        if (intstat & USBHSD_INTSTAT_DEV_INT_MASK) {
            if (reg_data & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
                if (ep1_armed) {
                    ep1_armed = false;
                    VPRINTF(LOW, "MCU: Bus reset - EP1 arm cleared\n");
                }
            }
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_DEV_INT_MASK);
        }

        // EP0 OUT interrupt: SETUP or status-phase OUT.
        if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();
                // Arm EP1 OUT after the first SETUP response (after
                // SET_CONFIGURATION), equivalent to the INTEN |= EP1OUT and
                // EP1 OUT arm after SET_CONFIGURATION.
                if (!ep1_armed) {
                    usb_ep1_out_arm();
                    ep1_armed = true;
                    VPRINTF(LOW, "MCU: EP1 OUT armed for iteration %d (expecting %d bytes)\n",
                            iter, iter);
                }
            }
        }

        // EP0 IN interrupt: clear it.
        if (intstat & USBHSD_INTSTAT_EP0IN_MASK) {
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);
        }

        // Track FRAME_INT: set flag whenever the SOF interrupt is observed.
        // FRAME_INT fires every 1 ms (SOF period). It is not guaranteed to
        // coincide with an EP1OUT event in the same INTSTAT read, so we
        // accumulate it across poll iterations and check the flag once per
        // EP1OUT completion instead of re-reading INTSTAT at that moment.
        if (intstat & USBHSD_INTSTAT_FRAME_INT_MASK) {
            frame_int_seen = true;
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_FRAME_INT_MASK);
        }

        // EP1 OUT transfer complete: detect via INTSTAT.EP1OUT bit.
        //
        // Previous approach polled Active=0 in the EP list entry, which
        // worked for iteration 1 but failed for iterations 2 onwards.
        // The re-arm writes Active=1 with the TR (toggle-reset) bit set
        // (bit 28). The USB HS device controller holds Active=1 for one
        // full SOF period (~125 us) after a TR re-arm so that the toggle
        // reset is synchronised to the next SOF boundary. During that
        // ~125 us window, Active stays 1 even though the previous DMA is
        // complete, so the Active=0 poll does not fire until one SOF after
        // the transfer ends. By then the host (running at #130us per packet)
        // has sent the next packet, overwriting the entry with the wrong
        // residual.
        //
        // INTSTAT.EP1OUT fires as soon as the DMA for the current transfer
        // completes - before any TR processing. With the host waiting
        // 130 us between packets the MCU has ample time (>110 us) to read
        // the entry and re-arm EP1 before the next OUT token arrives.
        if (ep1_armed && (intstat & USBHSD_INTSTAT_EP1OUT_MASK)) {
            entry = lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET);

            VPRINTF(LOW, "MCU: EP1OUT transfer complete (iteration %d)\n", iter);

            // Check that FRAME_INT was observed at least once since the last
            // EP1OUT completion (or since test start for iteration 1).
            // Uses the accumulated frame_int_seen flag rather than a live
            // INTSTAT re-read, because FRAME_INT fires every 125 us (SOF)
            // and is not guaranteed to coincide with the EP1OUT window.
            if (!frame_int_seen) {
                VPRINTF(LOW, "MCU: FAIL - FRAME_INT not seen before EP1OUT fired (iter %d)\n",
                        iter);
            } else {
                VPRINTF(LOW, "MCU: FRAME_INT confirmed seen before EP1OUT (iter %d)\n", iter);
            }
            frame_int_seen = false; // reset for the next iteration window

            // Clear EP1OUT status bit (W1C). FRAME_INT was already cleared
            // above when it was first observed in the poll loop.
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP1OUT_MASK);

            // entry was already latched above while Active=0.

            // Extract NBytes residual (bits [25:11]) and addr_offset field
            // (bits [10:0]).
            nbytes_residual   = (entry >> 11) & 0x7FFFu;
            addr_offset_field = entry & 0x7FFu;

            VPRINTF(LOW, "MCU: [iter %d] EP1 entry=0x%08x  residual=%d  addr_offset_field=0x%x\n",
                    iter, entry, nbytes_residual, addr_offset_field);

            errors = 0;

            // 1. Verify NBytes residual == 32 - i.
            // Host sends 'iter' bytes; NBytes was armed at 32, so residual
            // should be 32 - iter.
            if (nbytes_residual != (USB_HS_NBYTE_BUDGET - iter)) {
                VPRINTF(LOW, "MCU: FAIL [iter %d] residual=%d expected=%d\n",
                        iter, nbytes_residual, USB_HS_NBYTE_BUDGET - iter);
                errors++;
            }

            // 2. Verify the buffer address offset advanced by one 64-byte
            // chunk (short packet always consumes one full 64-byte slot).
            if (addr_offset_field != USB_EP1_ADDR_OFFSET_EXPECTED) {
                VPRINTF(LOW, "MCU: FAIL [iter %d] addr_offset_field=0x%x expected=0x%x\n",
                        iter, addr_offset_field, USB_EP1_ADDR_OFFSET_EXPECTED);
                errors++;
            }

            // 3. Verify the received byte pattern: buf[j] == j+1.
            // Mirrors: if (ep1out_byte_buf[j] != j+1) terminateTest(FAIL, ...)
            for (j = 0; j < iter; j++) {
                // Read the byte from the EP1 OUT SRAM buffer.
                // Each 32-bit word holds 4 bytes; extract the relevant byte.
                uint32_t word  = lsu_read_32(USB_DMA_BASE_ADDR
                                             + USB_SRAM_EP1_OUT_BUF_OFFSET
                                             + (j & ~3u));
                uint32_t shift = (j & 3u) * 8u;
                byte_val = (uint8_t)((word >> shift) & 0xFFu);
                if (byte_val != (uint8_t)(j + 1u)) {
                    VPRINTF(LOW,
                            "MCU: FAIL [iter %d] buf[%d]=0x%02x expected=0x%02x\n",
                            iter, j, byte_val, j + 1u);
                    errors++;
                }
            }

            if (errors == 0) {
                VPRINTF(LOW, "MCU: PASS iteration %d (residual=%d, pattern ok)\n",
                        iter, nbytes_residual);
            }

            iter++;

            if (iter <= USB_NBYTE_ITERATIONS) {
                // Re-fill the buffer with a known pattern before re-arming.
                for (i = 0; i < USB_HS_NBYTE_BUDGET; i += 4) {
                    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP1_OUT_BUF_OFFSET + i,
                                 0xDEDEDEDEu);
                }
                // Re-arm with Active=1, NBytes=0x20, toggle-reset for the next OUT.
                usb_ep1_out_rearm_toggle_reset();
                VPRINTF(LOW, "MCU: EP1 OUT re-armed for iteration %d\n", iter);
            }
        }

        // Periodic diagnostic log every 2000 iterations.
        if (poll_count % 2000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x iter=%d ep1_armed=%d\n",
                    poll_count, reg_data, intstat, iter, (int)ep1_armed);
        }
    }

    if (iter <= USB_NBYTE_ITERATIONS) {
        VPRINTF(LOW, "MCU: USB HS nbyte test - TIMEOUT at iteration %d\n", iter);
    } else {
        VPRINTF(LOW, "MCU: USB HS nbyte test - all %d iterations complete\n",
                USB_NBYTE_ITERATIONS);
    }

    reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT final = 0x%x\n", reg_data);
    VPRINTF(LOW, "MCU: USB HS nbyte test - halting\n");
    csr_write_mpmc_halt();
}
