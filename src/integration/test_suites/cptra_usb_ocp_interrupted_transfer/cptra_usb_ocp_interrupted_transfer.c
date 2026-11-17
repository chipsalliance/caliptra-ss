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

volatile char *stdout = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

#define INTERRUPTED_TRANSFER_MAILBOX_POLL_LIMIT 1000000u

// Private verification-channel commands, not OCP Recovery commands.
enum interrupted_transfer_opcode {
    OPCODE_READ_FIFO_BYTE = 0x05u,
    OPCODE_READ_BATCH_ABORTED = 0x06u,
};

static void fail_and_halt(const char *message)
{
    VPRINTF(FATAL, "%s\n", message);
    SEND_STDOUT_CTRL(0x1);
    while (1) {
    }
}

static uint8_t generation_is_newer(uint16_t generation,
                                   uint16_t previous_generation)
{
    uint16_t distance = (uint16_t)(generation - previous_generation);

    // Serial-number arithmetic accepts wrap but rejects duplicates and stale
    // generations, including the ambiguous half-space distance.
    return (distance != 0u) && (distance < 0x8000u);
}

void main(void)
{
    uint32_t command_word = 0u;
    uint32_t command_magic = 0u;
    uint32_t fifo_word = 0u;
    uint32_t write_index = 0u;
    uint32_t read_index = 0u;
    uint32_t fifo_size = 0u;
    uint16_t last_generation = 0u;
    uint16_t generation;
    uint8_t opcode;
    uint8_t fifo_status = 0u;
    uint8_t byte_index = 0u;
    uint8_t data;
    uint8_t aborted = 0u;
    uint8_t mailbox_released = 0u;

    VPRINTF(LOW, "CPTRA: OCP interrupted-transfer firmware start\n");
    soc_ifc_set_flow_status_field(
        SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    // Do not access Recovery registers until MCU enumeration and release.
    for (uint32_t poll = 0u;
         poll < INTERRUPTED_TRANSFER_MAILBOX_POLL_LIMIT;
         ++poll) {
        if (lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) &
            MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) {
            mailbox_released = 1u;
            break;
        }
    }
    if (!mailbox_released) {
        fail_and_halt("CPTRA: mailbox release timed out");
    }
    lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, (uint32_t)CMD_COMPLETE);

    if (cptra_usb_ocp_recovery_set_path_disable(0u) != 0u) {
        fail_and_halt("CPTRA: could not establish enabled OCP path");
    }
    cptra_usb_ocp_recovery_signal_state_generation(
        CPTRA_USB_OCP_FW_STATE_PATH_READY, 0u, 0u);

    while (1) {
        cptra_usb_ocp_recovery_read_fw_command(
            &command_word, &command_magic);
        if (command_magic != CPTRA_USB_OCP_FW_COMMAND_MAGIC) {
            continue;
        }
        generation = (uint16_t)((command_word >> 16) & 0xFFFFu);
        opcode = (uint8_t)((command_word >> 8) & 0xFFu);
        if (!generation_is_newer(generation, last_generation)) {
            continue;
        }
        last_generation = generation;
        data = 0u;

        switch (opcode) {
        case OPCODE_READ_FIFO_BYTE:
            if (byte_index == 0u) {
                if (cptra_usb_ocp_recovery_read_fifo_status(
                        &fifo_status, &write_index, &read_index,
                        &fifo_size) != 0u) {
                    fail_and_halt("CPTRA: FIFO status DMA read failed");
                }
                if ((fifo_size == 0u) || (write_index >= fifo_size) ||
                    (read_index >= fifo_size) ||
                    ((fifo_status &
                      RECOVERY_INDIRECT_FIFO_STATUS_0_EMPTY_MASK) != 0u)) {
                    fail_and_halt("CPTRA: FIFO empty or inconsistent");
                }
                if (cptra_usb_ocp_recovery_drain_fifo(
                        1u, &fifo_word, 1u) != 0u) {
                    fail_and_halt("CPTRA: FIFO DWORD DMA read failed");
                }
            }
            // Only the first fresh byte command pops a DWORD. The host checks
            // these bytes against its payload, independently of firmware.
            data = (uint8_t)(fifo_word >> (8u * byte_index));
            byte_index = (uint8_t)((byte_index + 1u) % sizeof(fifo_word));
            break;

        case OPCODE_READ_BATCH_ABORTED:
            if (cptra_usb_ocp_recovery_read_batch_aborted(&aborted) != 0u) {
                fail_and_halt("CPTRA: BATCH_ABORTED DMA read failed");
            }
            data = aborted;
            break;

        case CPTRA_USB_OCP_FW_COMMAND_FLOW_COMPLETE:
            if (byte_index != 0u) {
                fail_and_halt("CPTRA: completion with unpublished FIFO bytes");
            }
            cptra_usb_ocp_recovery_signal_state_generation(
                CPTRA_USB_OCP_FW_STATE_FLOW_COMPLETE, 0u, generation);
            cptra_usb_ocp_recovery_publish_completion();
            while (1) {
            }

        default:
            cptra_usb_ocp_recovery_signal_state_generation(
                CPTRA_USB_OCP_FW_STATE_COMMAND_ERROR, opcode, generation);
            fail_and_halt("CPTRA: unknown interrupted-transfer command");
        }

        cptra_usb_ocp_recovery_signal_state_generation(
            CPTRA_USB_OCP_FW_STATE_PATH_READY, data, generation);
    }
}
