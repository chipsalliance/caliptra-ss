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
// Description: shared firmware body for the USB error-injection test suites.
//
// WHY THIS FILE EXISTS
//
// The seven wire-corruption error tests (data_crc, token_crc, pid_check,
// pid_illegal, short_pkt, long_pkt, toggle) need IDENTICAL firmware: boot,
// enumerate, arm EP1 OUT, keep re-arming it, and never fail on a data
// mismatch. Only the banner text differs. Duplicating a 150-line poll loop
// seven times would mean seven places to fix the next time the EP0 re-arm
// rules change, so the loop lives here once and each suite's .c file is a
// thin wrapper that defines its name and includes this file.
//
// HOW IT DIFFERS FROM caliptra_ss_usb_hs_dev_bulk_out.c
//
// Two deliberate changes, both because the payload of the injected transfer
// is EXPECTED to be wrong or missing:
//
//   1. NO DATA CHECK. The bulk_out firmware verifies word[i] == i and reports
//      FAILED on a mismatch. Here a mismatch is the point of the test: a
//      corrupted CRC means the device discards the packet, a short packet
//      means fewer bytes arrived, a skewed toggle means the payload was ACKed
//      and thrown away. Checking it would turn every passing run into a
//      failure. What the firmware reports instead is the residual byte count,
//      which is useful debug when a bin does not close.
//
//   2. EP1 IS RE-ARMED EVERY TIME IT COMPLETES, not once. Each sequence drives
//      up to three transfers on EP1 (clean, injected, clean) and the hardware
//      clears ACTIVE after each one, so a single arm would leave the second
//      and third transfers NAKed forever and the recovery check would be
//      meaningless.
//
// The toggle-reset policy is the one documented at length in usb.h: TR is a
// LOAD, not a clear, and setting it mid-stream on a bulk OUT is a silent
// endpoint kill. So TR is set ONLY on the first arm after a bus reset, which
// is what the ep1_first_arm flag below tracks.
//
// WHY IT LIVES DIRECTLY IN libs/usb/ AND NOT IN A SUBDIRECTORY
//
// tools/scripts/Makefile builds the firmware with only -I$(BUILD_DIR) and
// populates BUILD_DIR from HEADER_FILES, whose USB entry is
//
//     $(foreach comp_lib, $(COMP_LIBS), $(wildcard $(comp_lib)/*.h))
//
// That glob is one level deep, so a header in libs/usb/<subdir>/ would never
// be copied into BUILD_DIR and the include below would not resolve. Hence the
// flat location next to usb.h.
//
// Usage from a suite .c file:
//   #define USB_ERR_INJECT_TEST_NAME "data CRC corruption"
//   #include "usb_err_inject_fw_common.h"

#ifndef USB_ERR_INJECT_FW_COMMON_H
#define USB_ERR_INJECT_FW_COMMON_H

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

#ifndef USB_ERR_INJECT_TEST_NAME
#error "USB_ERR_INJECT_TEST_NAME must be defined before including this file"
#endif

// Poll budget. Larger than the 30000 of the bulk OUT test because these
// sequences run three transfers back to back and one of them deliberately
// waits out a device response that never comes.
//
// This is now only a FALLBACK ceiling, not the normal exit. The loop ends on
// the host STOP handshake below; running the budget out is what happens when
// the host never sends it. See the MCU STOP note at the loop.
#define USB_ERR_POLL_TIMEOUT           60000u


// EP1 OUT buffer placed after the EP0 buffers, which occupy 0x000-0x1FF.
#define USB_SRAM_EP1_OUT_BUF_OFFSET    0x200u

// One HS bulk max packet plus headroom for a LONG_PACKET injection, which
// elongates the packet past wMaxPacketSize on purpose. 1024 keeps the whole
// buffer inside the 4096-byte USB SRAM (0x200..0x9FF).
#define USB_ERR_EP1_BUF_BYTES          1024u

// EP command/status list offset of the EP1 OUT descriptor. Same value the
// bulk OUT test uses; the list layout is 2 double-words per endpoint pair.
#define USB_EP_LIST_EP1_OUT_OFFSET     0x010u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// first_arm selects whether the data toggle is loaded. See the header note.
static void usb_err_ep1_out_arm(bool first_arm) {
    uint32_t ep1_out = USB_EP_ENTRY_ACTIVE
                     | USB_EP_ENTRY_NBYTES(USB_ERR_EP1_BUF_BYTES)
                     | USB_EP_ENTRY_ADDR(USB_SRAM_EP1_OUT_BUF_OFFSET);
    if (first_arm)
        ep1_out |= USB_EP_ENTRY_TOGGLE_RESET
                 | USB_EP_ENTRY_TOGGLE_VALUE_DATA0;
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET, ep1_out);
}

static uint32_t usb_err_ep1_out_read(void) {
    return lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET);
}

// Has the host told us it is finished with the device?
//
// Reuses the MCI generic-wire command channel from the OCP-recovery work, the
// same decode and ack shape as caliptra_ss_usb_fs_dev_lpm_l1_dev_wakeup and
// caliptra_ss_usb_hs_hub_int_ep_status_change: the command arrives on
// GENERIC_INPUT_WIRES_1 as magic[31:24] | opcode[23:20] | delta[19:16] |
// generation[15:0], and the ack goes back on GENERIC_OUTPUT_WIRES_1 with
// ACK_MAGIC substituted for MAGIC. The host holds the command asserted until
// it sees the ack, so this polling loop cannot miss it.
static bool usb_err_host_stop_seen(void) {
    uint32_t command = lsu_read_32(SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_1);

    if ((command >> USB_LEGACY_EP0_COMMAND_MAGIC_SHIFT) !=
            USB_LEGACY_EP0_COMMAND_MAGIC)
        return false;
    if (((command >> USB_LEGACY_EP0_COMMAND_OPCODE_SHIFT) &
            USB_LEGACY_EP0_COMMAND_NIBBLE_MASK) != USB_LEGACY_EP0_COMMAND_STOP)
        return false;

    lsu_write_32(SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1,
        ((uint32_t)USB_LEGACY_EP0_COMMAND_ACK_MAGIC <<
         USB_LEGACY_EP0_COMMAND_MAGIC_SHIFT) | (command & 0x00FFFFFFu));
    return true;
}

void main(void) {
    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t transfers_handled  = 0;
    uint32_t ep1_completions    = 0;
    bool     ep1_armed          = false;
    bool     ep1_first_arm      = true;
    bool     host_stop_seen     = false;


    VPRINTF(LOW, "=================\nMCU: USB error injection - %s\n=================\n\n",
            USB_ERR_INJECT_TEST_NAME);

    boot_mcu();
    boot_usb_core_hub();
    usb_hub_connect();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    // MCU STOP HANDSHAKE, AND WHY THE EXIT IS NOT A COMPLETION COUNT
    //
    // There is no local completion condition to stop on: a corrupted packet is
    // MEANT to be discarded, so "the transfer finished" never happens on the
    // injection leg, and stopping after the first EP1 completion would disarm
    // the endpoint before the injected transfer even arrives.
    //
    // The loop therefore ran to USB_ERR_POLL_TIMEOUT every time, which is what
    // made these tests cost ~7.7 ms of simulation each - all seven passing runs
    // landed inside a 1 us spread of each other, independently of the error
    // injected, because the cost was the loop count and not the stimulus.
    //
    // Now the host tells us when it is done, over the same MCI generic-wire
    // channel caliptra_ss_usb_fs_dev_lpm_l1_dev_wakeup uses. The poll ceiling
    // stays as a FALLBACK so a sequence without the handshake - or a testbench
    // with no observer interface wired - behaves exactly as before instead of
    // hanging.
    for (poll_count = 0;
         poll_count < USB_ERR_POLL_TIMEOUT && !host_stop_seen;
         poll_count++) {


        usb_handle_bus_reset();
        reg_data = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT);

        if (reg_data & DEV0_CSR_INTSTAT_DEV_INT_MASK) {
            uint32_t cmd = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
            if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
                if (ep1_armed) {
                    // A bus reset invalidates the arm AND zeroes the hardware
                    // toggle, so the next arm has to load it again.
                    ep1_armed     = false;
                    ep1_first_arm = true;
                    VPRINTF(LOW, "MCU: Bus reset - EP1 arm cleared\n");
                }
            }
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_DEV_INT_MASK);
        }

        if (reg_data & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0OUT_MASK);
            uint32_t cmd = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
            if (cmd & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();
                transfers_handled++;
                if (!ep1_armed) {
                    usb_err_ep1_out_arm(ep1_first_arm);
                    ep1_armed     = true;
                    ep1_first_arm = false;
                    VPRINTF(LOW, "MCU: EP1 OUT armed for %d bytes\n",
                            USB_ERR_EP1_BUF_BYTES);
                }
            } else {
                // Status-stage ZLP OUT of a control read completed and the
                // hardware cleared ACTIVE on the EP0 OUT descriptor. Without
                // this re-arm enumeration stalls after the first control read
                // and EP1 is never armed at all - see the same note in
                // caliptra_ss_usb_hs_dev_bulk_out.c.
                usb_ep0_arm_out();
            }
        }

        if (reg_data & DEV0_CSR_INTSTAT_EP0IN_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);
        }

        // EP1 OUT completion. Report the residual and re-arm. The residual is
        // the only interesting number here: a clean 1024-byte-buffer transfer
        // of 512 bytes leaves 512, a SHORT_PACKET injection leaves more, and a
        // transfer the device discarded leaves the buffer untouched.
        if (ep1_armed && (reg_data & DEV0_CSR_INTSTAT_EP1OUT_MASK)) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP1OUT_MASK);
            uint32_t ep1_entry = usb_err_ep1_out_read();
            uint32_t residual  = (ep1_entry >> 11) & 0x7FFFu;

            ep1_completions++;
            VPRINTF(LOW, "MCU: EP1 OUT completion %d - received %d bytes (residual %d)\n",
                    ep1_completions, USB_ERR_EP1_BUF_BYTES - residual, residual);

            // No data check on purpose - see the file header.
            usb_err_ep1_out_arm(false);
        }

        if (poll_count % 10000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x ep1_armed=%d completions=%d\n",
                    poll_count,
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT),
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT),
                    (int)ep1_armed, ep1_completions);
        }

        // Checked last so the current iteration still serviced the endpoints
        // before the loop exits.
        host_stop_seen = usb_err_host_stop_seen();
    }

    if (host_stop_seen)
        VPRINTF(LOW, "MCU: host STOP received after %d poll iterations; halting\n",
                poll_count);
    else
        VPRINTF(LOW, "MCU: no host STOP within %d poll iterations; halting anyway\n",
                poll_count);

    VPRINTF(LOW, "MCU: USB error injection - %s: %d control transfers, %d EP1 completions\n",
            USB_ERR_INJECT_TEST_NAME, transfers_handled, ep1_completions);

    VPRINTF(LOW, "MCU: USB error injection - halting\n");
    csr_write_mpmc_halt();
}

#endif // USB_ERR_INJECT_FW_COMMON_H

// File contains AI-generated response based on internal company sources
