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
// Description: USB hub EP0 unsupported-request test for Caliptra Subsystem
//              (High Speed)
//
//  Boots the MCU, patches ONE word of the hub SETUP-match table, initializes
//  the USB device controller and hub, brings up the Caliptra core, then runs
//  the standard EP0 poll loop while the UVM host drives nine control transfers
//  at the hub.
//
//  Every request under test is addressed to the HUB, not to USBDC0, and is
//  decoded entirely in the hub EP0 hardware (SETUP-match table in
//  usb_ep0_hub_descr.m.vhdl plus usb_ep0_handler.m.vhdl). No MCU firmware
//  involvement is needed for any of them, so the poll loop below just keeps
//  USBDC0 responsive and then runs out its timeout.
//
//  THE ONE THING THIS FIRMWARE DOES DO is the SETUP-table patch described
//  below. See the host sequence file
//  caliptra_ss_usb_hs_hub_ep0_unsupported_features_valid_port_sequence.svh section 3 and
//  docs/usb/usb_ep0_handler_coverage_map.md for the full derivation.


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

#define USB_POLL_TIMEOUT 5000

// -----------------------------------------------------------------------------
// Hub SETUP-match table patch: last row SETUP_MASK_MSB
//
// The hub SETUP-match table is four 32-bit words per supported request, and
// its last row for device 0 is SetAndTestHubPortFeature
// (usb_ep0_hub_descr.m.vhdl:421-425), hub table words 192..195:
//
//   word 192  X"00000CA3"  match  {bmRequestType=0xA3, bRequest=0x0C}
//   word 193  X"FFE040C3"  wValue mask 0xFFE0, setup_request 0x43, LAST bit set
//   word 194  X"00010000"  expected wIndex 0x0000, ROM wLength cap 0x0001
//   word 195  X"00000000"  wIndex MASK - every bit a DON'T-CARE
//
// Mask polarity is 1 = compared, 0 = don't-care
// (usb_ep0_handler.m.vhdl:228). With word 195 all zeroes the masked wIndex of
// the last row can never mismatch, so the STALL leg at
// usb_ep0_handler.m.vhdl:239-241 (FSM arc READ_SETUP_MASK_MSB -> SETUP_DONE)
// is unreachable - that is the coverage hole this test closes.
//
// The hub table is not a ROM at run time: C_EP0_ROM is only the reset value of
// the writable array ep0_mem (usb_ep0_hub_descr.m.vhdl:72, :476) and any word
// below C_NWORDS = 196 is writable from this aperture while hub_write_lock is
// 0 (:495-502). hub_write_lock is HUB_EN AND HUB_DCON (:528), so the write
// MUST happen before boot_usb_core_hub(), which calls
// usb_hub_init_and_connect() and sets HUB_EN.
//
// Word 195 sits at 0x2000_1000 + 4*195 = 0x2000_130C, which is inside the hub
// aperture (SOC_USB_COMBO_HUB_DESCRIPTOR_HIGH_END_ADDR = 0x2000_130F).
//
// Writing 0x0000FFFF makes wIndex fully compared against the expected 0x0000
// of word 194, so the host's SetAndTestHubPortFeature with wIndex = 0x0001
// matches the row on opcode and wValue and mismatches on wIndex.
//
// Deliberately defined HERE and not in libs/usb/usb.h: the patch must affect
// this test and nothing else, and no other test issues bRequest 0x0C.
// -----------------------------------------------------------------------------
#define USB_HUB_SETUP_LAST_ROW_MASK_MSB \
    (SOC_USB_COMBO_HUB_DESCRIPTOR_LOW_BASE_ADDR + (195u * 4u))
#define USB_HUB_SETUP_LAST_ROW_MASK_MSB_VAL 0x0000FFFFu

// Expected reset contents of the other three words of that row, used only to
// prove the patch is being applied to the row this test thinks it is. A row
// mismatch means the hub IP table layout moved and the patch address must be
// recomputed - see the coverage-map doc.
#define USB_HUB_SETUP_LAST_ROW_MATCH_LSB \
    (SOC_USB_COMBO_HUB_DESCRIPTOR_LOW_BASE_ADDR + (192u * 4u))
#define USB_HUB_SETUP_LAST_ROW_MATCH_LSB_VAL 0x00000CA3u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

// Storage for the symbols the ISR library declares extern.
volatile uint32_t intr_count;
volatile mcu_intr_received_s mcu_intr_rcv = {0};

// Never reset. A non-zero value at the end of main() sends exactly one
// TB_CMD_TEST_FAIL. TB_CMD_TEST_PASS is never sent: it $finish-es the
// simulation before the UVM final_phase and would mask the host-side verdict.
static uint32_t total_errors = 0;


#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


// -----------------------------------------------------------------------------
// Patch the SETUP_MASK_MSB of the last hub SETUP-match row. Must be called
// BEFORE boot_usb_core_hub(), while hub_write_lock is still 0.
// -----------------------------------------------------------------------------
static void usb_hub_patch_last_setup_row_mask(void) {
    uint32_t match_lsb;
    uint32_t mask_msb_before;
    uint32_t mask_msb_after;

    match_lsb       = lsu_read_32(USB_HUB_SETUP_LAST_ROW_MATCH_LSB);
    mask_msb_before = lsu_read_32(USB_HUB_SETUP_LAST_ROW_MASK_MSB);

    VPRINTF(LOW, "MCU: hub SETUP table patch - row@0x%x match_lsb=0x%x "
            "mask_msb(before)=0x%x\n",
            USB_HUB_SETUP_LAST_ROW_MATCH_LSB, match_lsb, mask_msb_before);

    // Layout sanity check. If this fires the hub table moved and the patch
    // address is stale, so the host step 8 STALL could never happen and the
    // failure would look like a DUT bug instead of a stale constant.
    if (match_lsb != USB_HUB_SETUP_LAST_ROW_MATCH_LSB_VAL) {
        VPRINTF(LOW, "MCU: FAIL - hub SETUP table last row match_lsb is 0x%x, "
                "expected 0x%x. The hub table layout moved; recompute the "
                "patch word index (see the coverage-map doc).\n",
                match_lsb, USB_HUB_SETUP_LAST_ROW_MATCH_LSB_VAL);
        total_errors++;
    }

    lsu_write_32(USB_HUB_SETUP_LAST_ROW_MASK_MSB,
                 USB_HUB_SETUP_LAST_ROW_MASK_MSB_VAL);

    mask_msb_after = lsu_read_32(USB_HUB_SETUP_LAST_ROW_MASK_MSB);

    VPRINTF(LOW, "MCU: hub SETUP table patch - mask_msb(after)=0x%x "
            "(expected 0x%x)\n",
            mask_msb_after, USB_HUB_SETUP_LAST_ROW_MASK_MSB_VAL);

    // The write is only effective while hub_write_lock is 0. If the read-back
    // does not stick, the patch silently did not happen and the host would
    // report step 8 as a missing STALL, so fail here instead.
    if (mask_msb_after != USB_HUB_SETUP_LAST_ROW_MASK_MSB_VAL) {
        VPRINTF(LOW, "MCU: FAIL - hub SETUP table patch did not stick "
                "(read back 0x%x). hub_write_lock (HUB_EN and HUB_DCON) must "
                "still be 0 at this point.\n", mask_msb_after);
        total_errors++;
    }
}


void main (void) {

    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t transfers_handled = 0;
    uint32_t usb_events;


    VPRINTF(LOW, "=================\nMCU: USB hub EP0 unsupported-request test\n=================\n\n");

    // Standard MCU boot sequence
    boot_mcu();

    // Patch the hub SETUP-match table BEFORE the hub is enabled. This is the
    // only firmware action the scenario needs; everything else below is the
    // standard hub bring-up plus EP0 poll loop.
    usb_hub_patch_last_setup_row_mask();

    // Initialize USB device controller BEFORE Caliptra bringup.
    // USB PHY and pull-up need time to settle while Caliptra boots.
    // boot_usb_core_hub() calls usb_hub_init_and_connect() internally, which
    // programs the HUB RAM descriptors and sets HUB_EN only (HUB_CONNECT
    // is deliberately deferred - see the usb_hub_connect() call below).
    boot_usb_core_hub();

    // Enable the USB interrupt (PIC vector 3) now that boot_usb_core_hub() has
    // programmed INTEN and cleared any stale INTSTAT bits.
    // Deliberately not init_interrupts(): that routine also writes the MCI
    // and I3C interrupt registers, and this early its I3C write to
    // 0x200040a8 does not complete, stalling the LSU pipeline before
    // mstatus.MIE is set. init_usb_interrupts() touches only vector 3.
    intr_count = 0;
    init_usb_interrupts();

    // Caliptra core bringup

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    // USBDC0's own EP list/DEVCMDSTAT/DCON are now fully programmed (end
    // of boot_usb_core_hub()), so it is safe to connect the hub upstream:
    // usb_hub_connect() sets HUB_CONNECT. Only after this call will the host
    // see the hub on the bus and begin enumerating it.
    usb_hub_connect();

    VPRINTF(LOW, "MCU: Caliptra core ready, entering USB event loop\n");

    // Read initial USB state
    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT = 0x%x\n", reg_data);
    reg_data = lsu_read_32(USB_DEV_INTSTAT);
    VPRINTF(LOW, "MCU: USB INTSTAT = 0x%x\n", reg_data);


    // --- Main USB event loop: poll for SETUP packets ---
    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {

        // Direct DEVCMDSTAT poll for bus reset (fallback - INTSTAT may not report DEV_INT)
        usb_handle_bus_reset();

        // Drain the ISR event vector. service_usb_intr() already read and
        // acknowledged INTSTAT, so the foreground loop must not touch INTSTAT
        // itself. Atomically snapshot and clear the whole event vector.
        usb_events = usb_event_vector_take(&mcu_intr_rcv.usb);

        // Check for device-level interrupts (bus reset, connect change)
        if (usb_events & DEV0_CSR_INTSTAT_DEV_INT_MASK) {

            uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
            VPRINTF(LOW, "MCU: DEV_INT - DEVCMDSTAT = 0x%x\n", cmd);
            if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
            }
            // No INTSTAT write here: service_usb_intr() already cleared it.
        }

        // Check for EP0 OUT interrupt (SETUP or data)
        if (usb_events & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);

            if (cmd & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
                // NOTE: do NOT VPRINTF before usb_handle_control_transfer.
                // Each VPRINTF adds ~1-2us; the host VIP gives up on IN
                // polling ~5us after the SETUP ACK. Logging is done inside
                // the handler AFTER the SETUP bit is cleared.
                usb_handle_control_transfer();
                transfers_handled++;
            } else {
                // Status-stage ZLP OUT for a control-read completed (no
                // SETUP set). HW cleared ACTIVE on the EP0 OUT descriptor;
                // re-arm it so the next SETUP packet is received instead
                // of NAK'd.
                usb_ep0_arm_out();
            }
        }


        // Periodic diagnostic dump
        if (poll_count % 1000 == 0 && poll_count > 0) {
            uint32_t diag_cmd     = lsu_read_32(USB_DEV_DEVCMDSTAT);
            uint32_t diag_int     = lsu_read_32(USB_DEV_INTSTAT);
            uint32_t ep0_out      = lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000);
            uint32_t ep0_in_diag  = lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008);

            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x EP0OUT=0x%x EP0IN=0x%x transfers=%d intr_cnt=%d\n",
                    poll_count, diag_cmd, diag_int, ep0_out, ep0_in_diag, transfers_handled, intr_count);
        }

        // No mcu_sleep here: the event vector check is a single DCCM load, so
        // the loop stays tight and USB events are picked up within ~1us of the
        // interrupt being taken.

    }

    // Report final state
    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT final = 0x%x\n", reg_data);
    reg_data = lsu_read_32(USB_DEV_INFO);
    VPRINTF(LOW, "MCU: USB INFO final = 0x%x\n", reg_data);

    // The hub table is frozen by now (HUB_EN and HUB_DCON are both set), so
    // this read-back also proves the patch survived the whole run.
    VPRINTF(LOW, "MCU: hub SETUP table last-row mask_msb final = 0x%x\n",
            lsu_read_32(USB_HUB_SETUP_LAST_ROW_MASK_MSB));

    VPRINTF(LOW, "MCU: USB hub EP0 unsupported-request test - transfers handled: %d\n",
            transfers_handled);

    // FAIL-only verdict. A console print is not a verdict: only
    // SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL) fails a run.
    if (total_errors != 0) {
        VPRINTF(LOW, "MCU: FAIL - USB hub EP0 unsupported-request test: %d error(s)\n",
                total_errors);
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }

    VPRINTF(LOW, "MCU: USB hub EP0 unsupported-request test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
