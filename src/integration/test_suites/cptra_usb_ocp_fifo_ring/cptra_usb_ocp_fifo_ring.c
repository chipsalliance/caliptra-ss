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
// Caliptra Core firmware for the USB OCP Recovery FIFO ring compliance test.
//
// Protocol flow (OCP Recovery v1.1 Sec 8.2.5 and Sec 9.2):
//   1. Wait for the MCU mailbox start signal, then acknowledge.
//   2. Poll IMAGE_SIZE from INDIRECT_FIFO_CTRL until non-zero.  The Recovery
//      Agent programs IMAGE_SIZE = FIFO_SIZE before the initial fill.
//   3. Poll INDIRECT_FIFO_STATUS until FULL.  FULL means the RA has pushed
//      FIFO_SIZE-1 DWORDs (all slots minus the one reserved for the modulo
//      ring invariant) into the FIFO.
//   4. Hold OCP_FIFO_RING_FULL_HOLD_CYCLES so the RA can observe the FULL
//      state and attempt the overflow write that must be rejected with a USB
//      NAK per OCP Recovery v1.1 Sec 8.2.5.
//   5. Consume exactly the first DWORD and validate it equals 0xC0DE0000
//      (pattern base with word_index 0).  This advances READ_INDEX by one
//      slot and unblocks the RA polling loop.
//   6. Poll INDIRECT_FIFO_STATUS until FULL again.  The RA detects READ_INDEX
//      advanced, pushes the final DWORD (word_index = FIFO_SIZE-1, value
//      0xC0DE_0000|(FIFO_SIZE-1)), and the FIFO returns to FULL.  Polling here
//      ensures the refill is committed before the drain below reads that slot.
//   7. Drain the remaining IMAGE_SIZE-1 DWORDs (word_index 1..IMAGE_SIZE-1)
//      one at a time via INDIRECT_FIFO_DATA, validating each word against the
//      deterministic pattern 0xC0DE_0000 | word_index.
//   8. Signal success by writing SS_GENERIC_FW_EXEC_CTRL_0[2].

#include <stdint.h>

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"
#include "soc_ifc.h"
#include "usb_ocp_recovery_cptra.h"

// Deterministic fill pattern base matching the RA sequence:
//   word[i] = OCP_FIFO_RING_PATTERN_BASE | i
#define OCP_FIFO_RING_PATTERN_BASE 0xC0DE0000u

// Polling rate for all bounded-wait loops (nop iterations per attempt).
#define OCP_FIFO_RING_POLL_DELAY_CYCLES 32u

// Maximum number of polling iterations for any single wait condition.
// At OCP_FIFO_RING_POLL_DELAY_CYCLES=32 and 400 MHz this allows ~16 ms of
// wall time, which is sufficient for USB control transfers in RTL simulation.
#define OCP_FIFO_RING_POLL_LIMIT 200000u

// Bitmask for the FULL flag in byte 0 of INDIRECT_FIFO_STATUS per
// OCP Recovery v1.1 Sec 9.2 (bit 1 of the STATUS byte).
#define OCP_FIFO_STATUS_FULL_MASK  (1u << 1)

// Signal bit in SS_GENERIC_FW_EXEC_CTRL_0 used to notify the simulation
// environment that firmware has completed successfully.
#define SS_GENERIC_FW_EXEC_CTRL_GO_MASK (1u << 2)

// OCP_FIFO_RING_FULL_HOLD_CYCLES controls the delay between observing the
// initial FULL state (step 3) and performing the first DWORD pop (step 5).
// This timing-only parameter must be long enough for the directed overflow
// transfer to receive NAK backpressure before firmware frees one FIFO slot.
#ifndef OCP_FIFO_RING_FULL_HOLD_CYCLES
#define OCP_FIFO_RING_FULL_HOLD_CYCLES 20000u
#endif

volatile char *stdout = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

static void spin_delay(uint32_t cycles)
{
    for (uint32_t i = 0u; i < cycles; ++i) {
        __asm__ volatile ("nop");
    }
}

static void fail_and_halt(const char *message)
{
    VPRINTF(FATAL, "%s\n", message);
    SEND_STDOUT_CTRL(0x1);
    while (1) {
    }
}

void main(void)
{
    uint32_t image_size_words = 0u;
    uint8_t  fifo_status      = 0u;
    uint32_t write_index      = 0u;
    uint32_t read_index       = 0u;
    uint32_t fifo_size        = 0u;
    uint32_t word             = 0u;
    uint32_t poll_count       = 0u;
    uint8_t  full_reached     = 0u;

    VPRINTF(LOW, "CPTRA: USB OCP FIFO ring consumer starting\n");

    // Signal readiness so the MCU can proceed with USB enumeration
    // before sending the mailbox start command.
    soc_ifc_set_flow_status_field(
        SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    // Step 1: Wait for the MCU mailbox start command, then acknowledge.
    // The mailbox start ensures USB enumeration is complete before DMA
    // activity begins, avoiding AXI bus contention on tend_to_end_delay.
    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) &
            MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 0u) {
        spin_delay(OCP_FIFO_RING_POLL_DELAY_CYCLES);
    }
    lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, (uint32_t)CMD_COMPLETE);
    VPRINTF(LOW, "CPTRA: mailbox start received and acknowledged\n");

    // Step 2: Poll IMAGE_SIZE from INDIRECT_FIFO_CTRL.
    // The RA programs IMAGE_SIZE = FIFO_SIZE before filling; firmware must
    // not assume any fixed depth per OCP Recovery v1.1 Sec 9.2.
    for (poll_count = 0u;
         (poll_count < OCP_FIFO_RING_POLL_LIMIT) && (image_size_words == 0u);
         ++poll_count) {
        image_size_words = cptra_usb_ocp_recovery_read_image_size_words();
        if (image_size_words == 0u) {
            spin_delay(OCP_FIFO_RING_POLL_DELAY_CYCLES);
        }
    }
    if (image_size_words == 0u) {
        fail_and_halt(
            "CPTRA: INDIRECT_FIFO_CTRL IMAGE_SIZE was not programmed");
    }
    VPRINTF(LOW, "CPTRA: IMAGE_SIZE=%u words\n", image_size_words);

    // Step 3: Poll INDIRECT_FIFO_STATUS until FULL.
    // FULL indicates the RA has completed the initial fill of FIFO_SIZE-1
    // DWORDs per OCP Recovery v1.1 Sec 8.2.5.
    full_reached = 0u;
    for (poll_count = 0u;
         poll_count < OCP_FIFO_RING_POLL_LIMIT;
         ++poll_count) {
        if (cptra_usb_ocp_recovery_read_fifo_status(
                &fifo_status, &write_index,
                &read_index, &fifo_size) != 0u) {
            fail_and_halt(
                "CPTRA: INDIRECT_FIFO_STATUS read failed during initial poll");
        }
        if ((fifo_status & OCP_FIFO_STATUS_FULL_MASK) != 0u) {
            full_reached = 1u;
            break;
        }
        spin_delay(OCP_FIFO_RING_POLL_DELAY_CYCLES);
    }
    if (!full_reached) {
        fail_and_halt(
            "CPTRA: FIFO did not become FULL after initial fill");
    }

    // Validate that FIFO_SIZE is consistent with the programmed IMAGE_SIZE.
    // Both values are runtime-discovered; no fixed depth is compiled in.
    if (fifo_size < 2u) {
        fail_and_halt("CPTRA: FIFO_SIZE < 2 is not a valid ring size");
    }
    if (image_size_words != fifo_size) {
        VPRINTF(FATAL,
                "CPTRA: IMAGE_SIZE=%u != FIFO_SIZE=%u\n",
                image_size_words, fifo_size);
        fail_and_halt("CPTRA: IMAGE_SIZE and FIFO_SIZE are inconsistent");
    }
    VPRINTF(LOW,
            "CPTRA: FIFO FULL confirmed: FIFO_SIZE=%u wi=%u ri=%u\n",
            fifo_size, write_index, read_index);

    // Step 4: Hold to allow the RA to observe FULL and attempt the overflow
    // write that must be rejected with a USB NAK per OCP Recovery v1.1
    // Sec 8.2.5.  OCP_FIFO_RING_FULL_HOLD_CYCLES is a timing-only knob.
    spin_delay(OCP_FIFO_RING_FULL_HOLD_CYCLES);

    // Step 5: Consume exactly word_index 0 (value 0xC0DE0000).
    // This advances READ_INDEX by one slot and unblocks the RA polling loop
    // that is waiting for READ_INDEX to change.
    word = 0u;
    if (cptra_usb_ocp_recovery_read_dword_retry(
            SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_DATA, &word) != 0u) {
        fail_and_halt("CPTRA: first FIFO DWORD read failed");
    }
    if (word != (OCP_FIFO_RING_PATTERN_BASE | 0u)) {
        VPRINTF(FATAL,
                "CPTRA: word[0] got 0x%08x expected 0x%08x\n",
                word, OCP_FIFO_RING_PATTERN_BASE);
        fail_and_halt("CPTRA: first FIFO DWORD content mismatch");
    }
    VPRINTF(LOW, "CPTRA: word[0] validated (0x%08x)\n", word);

    // Step 6: Poll INDIRECT_FIFO_STATUS until FULL again.
    // After the pop the RA detects READ_INDEX advanced, pushes the final
    // DWORD (word_index = FIFO_SIZE-1), and the FIFO returns to FULL.
    // Waiting for FULL here guarantees the refill is committed before
    // the drain loop below reads that slot.
    full_reached = 0u;
    for (poll_count = 0u;
         poll_count < OCP_FIFO_RING_POLL_LIMIT;
         ++poll_count) {
        if (cptra_usb_ocp_recovery_read_fifo_status(
                &fifo_status, &write_index,
                &read_index, &fifo_size) != 0u) {
            fail_and_halt(
                "CPTRA: INDIRECT_FIFO_STATUS read failed during refill poll");
        }
        if ((fifo_status & OCP_FIFO_STATUS_FULL_MASK) != 0u) {
            full_reached = 1u;
            break;
        }
        spin_delay(OCP_FIFO_RING_POLL_DELAY_CYCLES);
    }
    if (!full_reached) {
        fail_and_halt(
            "CPTRA: FIFO did not return to FULL after RA refill");
    }
    VPRINTF(LOW,
            "CPTRA: FIFO FULL after refill: wi=%u ri=%u\n",
            write_index, read_index);

    // Step 7: Drain remaining IMAGE_SIZE-1 DWORDs (word_index 1..IMAGE_SIZE-1).
    // The FIFO is guaranteed FULL at this point so all IMAGE_SIZE-1 slots are
    // available; no per-word flow control is required.
    for (uint32_t i = 1u; i < image_size_words; ++i) {
        uint32_t expected = OCP_FIFO_RING_PATTERN_BASE | i;
        word = 0u;
        if (cptra_usb_ocp_recovery_read_dword_retry(
                SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_DATA,
                &word) != 0u) {
            VPRINTF(FATAL,
                    "CPTRA: FIFO DWORD read failed at word_index=%u\n", i);
            fail_and_halt("CPTRA: FIFO drain read failed");
        }
        if (word != expected) {
            VPRINTF(FATAL,
                    "CPTRA: word[%u] got 0x%08x expected 0x%08x\n",
                    i, word, expected);
            fail_and_halt("CPTRA: FIFO ring data ordering mismatch");
        }
    }

    VPRINTF(LOW,
            "CPTRA: verified all %u FIFO ring words in order\n",
            image_size_words);

    // Step 8: Signal success.  The RA is polling INDIRECT_FIFO_STATUS for
    // EMPTY (READ_INDEX == WRITE_INDEX); draining IMAGE_SIZE words leaves
    // the ring in the EMPTY state that satisfies that condition.
    lsu_write_32(
        CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0,
        SS_GENERIC_FW_EXEC_CTRL_GO_MASK);

    while (1) {
    }
}
