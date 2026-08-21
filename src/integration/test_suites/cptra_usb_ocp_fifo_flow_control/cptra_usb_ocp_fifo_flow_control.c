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

#include <stdint.h>

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"
#include "soc_ifc.h"
#include "usb_ocp_recovery_cptra.h"

#ifndef OCP_FIFO_FLOW_INITIAL_DELAY_CYCLES
#define OCP_FIFO_FLOW_INITIAL_DELAY_CYCLES 12000u
#endif

#ifndef OCP_FIFO_FLOW_WORDS_PER_SERVICE
#define OCP_FIFO_FLOW_WORDS_PER_SERVICE 4u
#endif

#ifndef OCP_FIFO_FLOW_INTER_SERVICE_DELAY_CYCLES
#define OCP_FIFO_FLOW_INTER_SERVICE_DELAY_CYCLES 3000u
#endif

#define OCP_FIFO_FLOW_FINAL_VALID_BYTES 3u

#define OCP_FIFO_FLOW_PATTERN_BASE 0xC0DE0000u
#define OCP_FIFO_FLOW_POLL_DELAY_CYCLES 32u
#define OCP_FIFO_FLOW_POLL_LIMIT 200000u
#define SS_GENERIC_FW_EXEC_CTRL_GO_MASK (1u << 2)

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
    for (uint32_t iteration = 0u; iteration < cycles; ++iteration) {
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
    uint32_t poll_count = 0u;

    VPRINTF(LOW, "CPTRA: USB OCP FIFO flow-control consumer starting\n");
    soc_ifc_set_flow_status_field(
        SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) &
            MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 0u) {
        spin_delay(OCP_FIFO_FLOW_POLL_DELAY_CYCLES);
    }
    lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, (uint32_t)CMD_COMPLETE);

    // OCP Recovery v1.1 Sections 8.2.5 and 9.2 define IMAGE_SIZE as
    // protocol state programmed by the Recovery Agent in INDIRECT_FIFO_CTRL.
    while ((image_size_words == 0u) &&
           (poll_count < OCP_FIFO_FLOW_POLL_LIMIT)) {
        image_size_words =
            cptra_usb_ocp_recovery_read_image_size_words();
        poll_count++;
        spin_delay(OCP_FIFO_FLOW_POLL_DELAY_CYCLES);
    }
    if (image_size_words == 0u) {
        fail_and_halt("CPTRA: FIFO flow image size was not programmed");
    }

    spin_delay(OCP_FIFO_FLOW_INITIAL_DELAY_CYCLES);
    VPRINTF(LOW, "CPTRA: draining %u FIFO flow-control words\n",
             image_size_words);
    for (uint32_t index = 0u; index < image_size_words; ++index) {
        uint32_t word = 0u;
        uint32_t expected = OCP_FIFO_FLOW_PATTERN_BASE | index;

        // The EXT read is held until the current FIFO batch becomes available.
        // This is the architectural synchronization point between the USB
        // producer and Caliptra consumer.
        if (cptra_usb_ocp_recovery_read_dword_retry(
                SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_DATA,
                &word) != 0u) {
            fail_and_halt("CPTRA: FIFO data read failed");
        }
        if (((index + 1u) == image_size_words) &&
            (OCP_FIFO_FLOW_FINAL_VALID_BYTES < 4u)) {
            uint32_t valid_mask =
                (1u << (OCP_FIFO_FLOW_FINAL_VALID_BYTES * 8u)) - 1u;
            expected &= valid_mask;
        }
        if (word != expected) {
            VPRINTF(FATAL,
                    "CPTRA: FIFO word %u got 0x%08x expected 0x%08x\n",
                    index, word, expected);
            fail_and_halt("CPTRA: FIFO data ordering mismatch");
        }

        if ((((index + 1u) % OCP_FIFO_FLOW_WORDS_PER_SERVICE) == 0u) &&
            ((index + 1u) < image_size_words)) {
            spin_delay(OCP_FIFO_FLOW_INTER_SERVICE_DELAY_CYCLES);
        }
    }

    VPRINTF(LOW, "CPTRA: verified %u FIFO flow-control words\n",
             image_size_words);
    spin_delay(10000u);
    lsu_write_32(
        CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0,
        SS_GENERIC_FW_EXEC_CTRL_GO_MASK);
    while (1) {
    }
}
