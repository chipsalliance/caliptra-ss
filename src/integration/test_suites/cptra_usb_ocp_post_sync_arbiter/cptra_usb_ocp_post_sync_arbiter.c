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

#define PATH_CONTROL_MAILBOX_POLL_LIMIT 1000000u

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

    // Serial-number arithmetic permits wrap while rejecting duplicates and
    // values more than half of the 16-bit sequence space behind the current
    // generation.
    return (distance != 0u) && (distance < 0x8000u);
}

void main(void)
{
    uint32_t command_word = 0u;
    uint32_t command_magic = 0u;
    uint16_t generation;
    uint16_t last_generation = 0u;
    uint8_t opcode;
    uint8_t disabled;
    uint8_t result;
    uint8_t mailbox_released = 0u;

    VPRINTF(LOW, "CPTRA: OCP arbiter path-control firmware start\n");

    soc_ifc_set_flow_status_field(
        SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    // Recovery-register traffic begins only after the MCU has completed USB
    // enumeration and releases Caliptra through the mailbox command.
    for (uint32_t poll = 0u;
         poll < PATH_CONTROL_MAILBOX_POLL_LIMIT;
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

    result = cptra_usb_ocp_recovery_set_path_disable(0u);
    if (result != 0u) {
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

        if (opcode == CPTRA_USB_OCP_FW_COMMAND_SET_PATH_DISABLE) {
            disabled = 1u;
        } else if (
            opcode == CPTRA_USB_OCP_FW_COMMAND_CLEAR_PATH_DISABLE) {
            disabled = 0u;
        } else {
            cptra_usb_ocp_recovery_signal_state_generation(
                CPTRA_USB_OCP_FW_STATE_COMMAND_ERROR,
                opcode,
                generation);
            last_generation = generation;
            continue;
        }

        result = cptra_usb_ocp_recovery_set_path_disable(disabled);
        if (result != 0u) {
            fail_and_halt("CPTRA: OCP path-disable write/readback failed");
        }
        cptra_usb_ocp_recovery_signal_state_generation(
            disabled ?
                CPTRA_USB_OCP_FW_STATE_PATH_DISABLED :
                CPTRA_USB_OCP_FW_STATE_PATH_ENABLED,
            disabled,
            generation);
        last_generation = generation;
    }
}
