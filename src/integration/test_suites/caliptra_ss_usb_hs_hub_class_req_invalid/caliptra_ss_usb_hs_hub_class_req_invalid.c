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
// Description: USB hub class-request INVALID test for Caliptra Subsystem (High Speed)
//
//  Same bring-up and EP0 poll loop as caliptra_ss_usb_hs_hub_class_req_stall.
//  Every request under test is a hub CLASS request addressed to the HUB and is
//  decided in hardware (usb_ep0_handler SETUP-table walk, then
//  usb_app_hw_hub PROC_CLASS_STALL / PROC_REQUEST_HANDLING), so the firmware
//  takes no part in the decode.
//
//  THE ONE THING THIS FIRMWARE DOES DO is patch the opcode byte of ONE hub
//  SETUP-match row before the hub is enabled, so that the host step 23
//  GetHubStatus presents ep0_request = 0x72 to usb_app_hw_hub. No shipped row
//  has ep0_request bits 5:4 set, so without this patch the EP0_REQUEST[5:4]
//  toggle bins of usb_app_hw_hub are unreachable from the bus.
//
//  USB_POLL_TIMEOUT is 10000, twice the parent's 5000: the host sequence is
//  the parent's nine control transfers plus about 22 more, all EP0 with at
//  most a 4-byte data stage.


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

#define USB_POLL_TIMEOUT 4000

// -----------------------------------------------------------------------------
// Hub SETUP-match table patch: GetHubStatus row opcode
//
// The hub SETUP-match table is four 32-bit words per request and starts at hub
// table word 96 (USB_HUB_SETUP_TABLE_BASE, base + 0x180). Walking
// usb_ep0_hub_descr.m.vhdl func_ep0_rom, the GetHubStatus row is the 16th
// row, words 156..159:
//
//   word 156  X"000000A0"  match  {bmRequestType=0xA0, bRequest=0x00}
//   word 157  X"FFFF4042"  wValue mask 0xFFFF, data buffer 0x40,
//                          setup_request 0x42 (C_CLASS_REQ_GET_STATUS), LAST=0
//   word 158  X"00040000"  expected wIndex 0x0000, ROM wLength cap 4
//   word 159  X"0000FFFF"  wIndex mask
//
// usb_ep0_handler.m.vhdl:192 copies bits 6:0 of word 157 into setup_request,
// which IS ep0_request at the usb_app_hw_hub boundary. Rewriting bits 6:0 from
// 0x42 to 0x72 keeps bit 7 (LAST) clear and bits 15:8 (data buffer 0x40,
// which routes the IN data to ep0_class_rdata) unchanged, so the transfer
// still completes and returns hub_status(data_index), but ep0_request now has
// bits 6:4 = 111. 0x72 matches no class arm (falls into "when others => null"
// in both PROC_CLASS_STALL and PROC_REQUEST_HANDLING) and no standard arm in
// usb_ep0_handler PROC_STD_REQ_DECODE, so the request is NOT stalled and has
// no side effect.
//
// Word 157 sits at 0x2000_1000 + 4*157 = 0x2000_1274, inside the hub aperture.
// The table is writable only while hub_write_lock (HUB_EN and HUB_DCON) is 0,
// so the patch MUST run before boot_usb_core_hub(). usb_hub_init_and_connect()
// rewrites descriptor words only, never a SETUP row, so the patch survives.
//
// Containment: no other test is affected (run-time write in this image only),
// and neither hub_enum_stepA nor the parent class_req_stall steps issue
// GetHubStatus (bmRequestType 0xA0, bRequest 0x00).
//
// FS note for any sibling: the FS table has no QUALIFIER / OTHER_SPEED blocks,
// so the word index differs. Recompute, never copy.
// -----------------------------------------------------------------------------
#define USB_HUB_GETHUBSTATUS_ROW_MATCH_LSB \
    (SOC_USB_COMBO_HUB_DESCRIPTOR_LOW_BASE_ADDR + (156u * 4u))
#define USB_HUB_GETHUBSTATUS_ROW_MATCH_LSB_VAL 0x000000A0u

#define USB_HUB_GETHUBSTATUS_ROW_MASK_LSB \
    (SOC_USB_COMBO_HUB_DESCRIPTOR_LOW_BASE_ADDR + (157u * 4u))
#define USB_HUB_GETHUBSTATUS_ROW_MASK_LSB_VAL     0xFFFF4042u
#define USB_HUB_GETHUBSTATUS_ROW_MASK_LSB_PATCHED 0xFFFF4072u

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
// Patch the opcode of the GetHubStatus SETUP-match row. Must be called BEFORE
// boot_usb_core_hub(), while hub_write_lock is still 0.
// -----------------------------------------------------------------------------
static void usb_hub_patch_gethubstatus_opcode(void) {
    uint32_t match_lsb;
    uint32_t mask_lsb_before;
    uint32_t mask_lsb_after;

    match_lsb       = lsu_read_32(USB_HUB_GETHUBSTATUS_ROW_MATCH_LSB);
    mask_lsb_before = lsu_read_32(USB_HUB_GETHUBSTATUS_ROW_MASK_LSB);

    VPRINTF(LOW, "MCU: hub SETUP table patch - row@0x%x match_lsb=0x%x "
            "mask_lsb(before)=0x%x\n",
            USB_HUB_GETHUBSTATUS_ROW_MATCH_LSB, match_lsb, mask_lsb_before);

    // Layout sanity checks. If either fires the hub table moved and the patch
    // address is stale; the host step 23 would then silently miss the
    // EP0_REQUEST[5:4] toggle, so report it here as a stale constant rather
    // than leaving it to look like a coverage hole.
    if (match_lsb != USB_HUB_GETHUBSTATUS_ROW_MATCH_LSB_VAL) {
        VPRINTF(LOW, "MCU: FAIL - GetHubStatus row match_lsb is 0x%x, expected "
                "0x%x. The hub table layout moved; recompute the word index.\n",
                match_lsb, USB_HUB_GETHUBSTATUS_ROW_MATCH_LSB_VAL);
        total_errors++;
    }
    if (mask_lsb_before != USB_HUB_GETHUBSTATUS_ROW_MASK_LSB_VAL) {
        VPRINTF(LOW, "MCU: FAIL - GetHubStatus row mask_lsb is 0x%x, expected "
                "0x%x. The hub table layout moved; recompute the word index.\n",
                mask_lsb_before, USB_HUB_GETHUBSTATUS_ROW_MASK_LSB_VAL);
        total_errors++;
    }

    lsu_write_32(USB_HUB_GETHUBSTATUS_ROW_MASK_LSB,
                 USB_HUB_GETHUBSTATUS_ROW_MASK_LSB_PATCHED);

    mask_lsb_after = lsu_read_32(USB_HUB_GETHUBSTATUS_ROW_MASK_LSB);

    VPRINTF(LOW, "MCU: hub SETUP table patch - mask_lsb(after)=0x%x "
            "(expected 0x%x)\n",
            mask_lsb_after, USB_HUB_GETHUBSTATUS_ROW_MASK_LSB_PATCHED);

    // The write only takes effect while hub_write_lock is 0. A read-back
    // mismatch means the patch did not happen.
    if (mask_lsb_after != USB_HUB_GETHUBSTATUS_ROW_MASK_LSB_PATCHED) {
        VPRINTF(LOW, "MCU: FAIL - hub SETUP table patch did not stick "
                "(read back 0x%x). hub_write_lock (HUB_EN and HUB_DCON) must "
                "still be 0 at this point.\n", mask_lsb_after);
        total_errors++;
    }
}


void main (void) {

    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t transfers_handled = 0;
    uint32_t usb_events;


    VPRINTF(LOW, "=================\nMCU: USB hub class-request INVALID test\n=================\n\n");

    // Standard MCU boot sequence
    boot_mcu();

    // Patch the hub SETUP-match table BEFORE the hub is enabled.
    usb_hub_patch_gethubstatus_opcode();

    // Initialize USB device controller BEFORE Caliptra bringup.
    // boot_usb_core_hub() calls usb_hub_init_and_connect() internally, which
    // programs the HUB RAM descriptors and sets HUB_EN only (HUB_CONNECT
    // is deliberately deferred - see the usb_hub_connect() call below).
    boot_usb_core_hub();

    // Enable the USB interrupt (PIC vector 3) only - see
    // caliptra_ss_usb_hs_hub_class_req_stall.c for why not init_interrupts().
    intr_count = 0;
    init_usb_interrupts();

    // Caliptra core bringup
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    // USBDC0 is fully programmed, so it is safe to connect the hub upstream.
    usb_hub_connect();

    VPRINTF(LOW, "MCU: Caliptra core ready, entering USB event loop\n");

    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT = 0x%x\n", reg_data);
    reg_data = lsu_read_32(USB_DEV_INTSTAT);
    VPRINTF(LOW, "MCU: USB INTSTAT = 0x%x\n", reg_data);


    // --- Main USB event loop: poll for SETUP packets ---
    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {

        // Direct DEVCMDSTAT poll for bus reset (fallback - INTSTAT may not report DEV_INT)
        usb_handle_bus_reset();

        // Atomically drain the ISR mailbox. service_usb_intr() already
        // acknowledged INTSTAT.
        usb_events = usb_event_vector_take(&mcu_intr_rcv.usb);

        if (usb_events & DEV0_CSR_INTSTAT_DEV_INT_MASK) {
            uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
            VPRINTF(LOW, "MCU: DEV_INT - DEVCMDSTAT = 0x%x\n", cmd);
            if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
            }
        }

        if (usb_events & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);

            if (cmd & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
                // Do NOT VPRINTF before usb_handle_control_transfer (timing).
                usb_handle_control_transfer();
                transfers_handled++;
            } else {
                // Status-stage ZLP OUT completed: re-arm EP0 OUT.
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
    }

    // Report final state
    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT final = 0x%x\n", reg_data);
    reg_data = lsu_read_32(USB_DEV_INFO);
    VPRINTF(LOW, "MCU: USB INFO final = 0x%x\n", reg_data);

    // The hub table is frozen by now, so this also proves the patch survived.
    VPRINTF(LOW, "MCU: hub SETUP table GetHubStatus row mask_lsb final = 0x%x\n",
            lsu_read_32(USB_HUB_GETHUBSTATUS_ROW_MASK_LSB));

    VPRINTF(LOW, "MCU: USB hub class-request INVALID test - transfers handled: %d\n",
            transfers_handled);

    // FAIL-only verdict. Only SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL) fails a run.
    if (total_errors != 0) {
        VPRINTF(LOW, "MCU: FAIL - USB hub class-request INVALID test: %d error(s)\n",
                total_errors);
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }

    VPRINTF(LOW, "MCU: USB hub class-request INVALID test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
