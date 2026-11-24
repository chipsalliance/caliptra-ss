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

#define FIFO_BOUNDARY_POLL_LIMIT 200000u
#define FIFO_BOUNDARY_PATTERN_BASE 0xC0DE0000u
// OCP Recovery v1.1 Section 9.1 DEVICE_STATUS/RECOVERY_STATUS.
#define FIFO_BOUNDARY_RECOVERY_MODE 0x03u
#define FIFO_BOUNDARY_RECOVERY_PENDING 0x04u
#define FIFO_BOUNDARY_AWAITING_IMAGE 0x01u

volatile char *stdout = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

static void spin_delay(void)
{
    for (uint32_t i = 0u; i < 32u; ++i) {
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

static void wait_command(uint8_t expected_opcode, uint16_t generation)
{
    for (uint32_t poll = 0u; poll < FIFO_BOUNDARY_POLL_LIMIT; ++poll) {
        uint32_t command = 0u;
        uint32_t magic = 0u;
        cptra_usb_ocp_recovery_read_fw_command(&command, &magic);
        if ((magic == CPTRA_USB_OCP_FW_COMMAND_MAGIC) &&
            ((uint16_t)(command >> 16) == generation)) {
            if ((uint8_t)(command >> 8) != expected_opcode) {
                fail_and_halt("CPTRA: unexpected FIFO boundary command");
            }
            return;
        }
        spin_delay();
    }
    fail_and_halt("CPTRA: FIFO boundary command timed out");
}

static void wait_command_release(void)
{
    for (uint32_t poll = 0u; poll < FIFO_BOUNDARY_POLL_LIMIT; ++poll) {
        uint32_t command = 0u;
        uint32_t magic = 0u;
        cptra_usb_ocp_recovery_read_fw_command(&command, &magic);
        if (magic != CPTRA_USB_OCP_FW_COMMAND_MAGIC) {
            return;
        }
        spin_delay();
    }
    fail_and_halt("CPTRA: FIFO boundary command release timed out");
}

static void publish_status(uint8_t device_status)
{
    if (cptra_usb_ocp_recovery_write_device_status(device_status, 0u) != 0u ||
        cptra_usb_ocp_recovery_write_recovery_status(
            FIFO_BOUNDARY_AWAITING_IMAGE, 0u, 0u) != 0u) {
        fail_and_halt("CPTRA: FIFO boundary status publication failed");
    }
}

void main(void)
{
    uint16_t generation = 0u;
    soc_ifc_set_flow_status_field(
        SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);
    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) &
            MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 0u) {
        spin_delay();
    }
    lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, (uint32_t)CMD_COMPLETE);
    publish_status(FIFO_BOUNDARY_RECOVERY_MODE);
    cptra_usb_ocp_recovery_signal_state_generation(
        CPTRA_USB_OCP_FW_STATE_PATH_READY, 0u, generation);

    for (uint32_t case_id = 1u; case_id <= 5u; ++case_id) {
        uint32_t image_words = 0u;
        uint32_t drained = 0u;
        do {
            uint8_t fifo_status = 0u;
            uint32_t write_index = 0u;
            uint32_t read_index = 0u;
            uint32_t fifo_words = 0u;
            uint32_t window_words;

            // Hold consumption until UVM has checked every committed chunk.
            // Image size and window capacity still come from protocol state.
            wait_command(CPTRA_USB_OCP_FW_COMMAND_FLOW_ADVANCE, ++generation);
            if (drained == 0u) {
                image_words = cptra_usb_ocp_recovery_read_image_size_words();
                if (image_words == 0u) {
                    fail_and_halt("CPTRA: FIFO boundary IMAGE_SIZE is zero");
                }
            }
            if (cptra_usb_ocp_recovery_read_fifo_status(
                    &fifo_status, &write_index, &read_index, &fifo_words) != 0u ||
                fifo_words == 0u) {
                fail_and_halt("CPTRA: FIFO boundary capacity discovery failed");
            }
            if (cptra_usb_ocp_recovery_wait_payload_available(
                    FIFO_BOUNDARY_POLL_LIMIT) != 0u) {
                fail_and_halt("CPTRA: FIFO boundary payload was not published");
            }
            window_words = image_words - drained;
            if (window_words > fifo_words) {
                window_words = fifo_words;
            }
            for (uint32_t i = 0u; i < window_words; ++i) {
                uint32_t word = 0u;
                uint32_t index = drained + i;
                uint32_t expected = FIFO_BOUNDARY_PATTERN_BASE | index;
                // FIFO_003 explicitly expects the integration's zero-filled
                // unused terminal byte; all preceding DWORDs remain intact.
                if ((case_id == 3u) && ((index + 1u) == image_words)) {
                    expected &= 0x00FFFFFFu;
                }
                if (cptra_usb_ocp_recovery_read_dword_retry(
                        SOC_USB_COMBO_RECOVERY_INDIRECT_FIFO_DATA, &word) != 0u) {
                    fail_and_halt("CPTRA: FIFO boundary drain failed");
                }
                if (word != expected) {
                    VPRINTF(FATAL,
                            "CPTRA: FIFO_%03u word[%u]=0x%08x expected=0x%08x\n",
                            case_id, index, word, expected);
                    fail_and_halt("CPTRA: FIFO boundary content mismatch");
                }
            }
            drained += window_words;
            VPRINTF(LOW, "CPTRA: FIFO_%03u verified %u/%u DWORDs\n",
                    case_id, drained, image_words);
            if (drained == image_words) {
                publish_status(FIFO_BOUNDARY_RECOVERY_PENDING);
            }
            cptra_usb_ocp_recovery_signal_state_generation(
                (drained == image_words) ?
                    CPTRA_USB_OCP_FW_STATE_RECOVERY_PENDING :
                    CPTRA_USB_OCP_FW_STATE_PATH_READY,
                (uint8_t)case_id, generation);
            wait_command_release();
        } while (drained < image_words);

        wait_command(CPTRA_USB_OCP_FW_COMMAND_FLOW_COMPLETE, ++generation);
        if (case_id < 5u) {
            publish_status(FIFO_BOUNDARY_RECOVERY_MODE);
        }
        cptra_usb_ocp_recovery_signal_state_generation(
            (case_id == 5u) ? CPTRA_USB_OCP_FW_STATE_FLOW_COMPLETE :
                              CPTRA_USB_OCP_FW_STATE_PATH_READY,
            (uint8_t)case_id, generation);
        wait_command_release();
    }
    cptra_usb_ocp_recovery_publish_completion();
    while (1) {
    }
}
