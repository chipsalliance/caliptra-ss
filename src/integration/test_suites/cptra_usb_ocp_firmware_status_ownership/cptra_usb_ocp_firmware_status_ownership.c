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

#define STATUS_OWNERSHIP_STATE_READY 0x40u
#define STATUS_OWNERSHIP_STATE_PROTECTED 0x41u
#define STATUS_OWNERSHIP_STATE_DONE 0x42u

#define STATUS_OWNERSHIP_DEVICE_STATUS_RECOVERY_MODE 0x03u
#define STATUS_OWNERSHIP_DEVICE_STATUS_RECOVERY_PENDING 0x04u
#define STATUS_OWNERSHIP_DEVICE_STATUS_RUNNING_RECOVERY 0x05u
#define STATUS_OWNERSHIP_DEVICE_STATUS_BOOT_FAILURE 0x0Eu
#define STATUS_OWNERSHIP_DEVICE_STATUS_FATAL_ERROR 0x0Fu

#define STATUS_OWNERSHIP_RECOVERY_STATUS_AWAITING_IMAGE 0x01u
#define STATUS_OWNERSHIP_RECOVERY_STATUS_BOOTING_IMAGE 0x02u
#define STATUS_OWNERSHIP_RECOVERY_STATUS_SUCCESS 0x03u
#define STATUS_OWNERSHIP_RECOVERY_STATUS_AUTH_ERROR 0x0Du
#define STATUS_OWNERSHIP_RECOVERY_STATUS_FAILED 0x0Cu

#define STATUS_OWNERSHIP_REC_REASON_NONE 0x0000u
#define STATUS_OWNERSHIP_REC_REASON_AUTH_RECOVERY_FW 0x000Fu
#define STATUS_OWNERSHIP_REC_REASON_FORCED_RECOVERY 0x0011u
#define STATUS_OWNERSHIP_REC_REASON_FLASHLESS_BOOT 0x0012u

#define STATUS_OWNERSHIP_HW_STATUS_FATAL_ERR (1u << 2)
#define STATUS_OWNERSHIP_PROT_ERROR_MASK 0x0000FF00u
#define STATUS_OWNERSHIP_PROT_ERROR_SHIFT 8u
#define STATUS_OWNERSHIP_STORAGE_MASK 0xFFFF00FFu
#define STATUS_OWNERSHIP_POLL_LIMIT 200000u

typedef struct {
    uint8_t device_status;
    uint16_t reason_code;
    uint8_t recovery_status;
    uint8_t image_index;
    uint8_t vendor_status;
    uint32_t hw_status;
} status_ownership_milestone_t;

static const status_ownership_milestone_t status_ownership_milestones[] = {
    {
        STATUS_OWNERSHIP_DEVICE_STATUS_RECOVERY_MODE,
        STATUS_OWNERSHIP_REC_REASON_FORCED_RECOVERY,
        STATUS_OWNERSHIP_RECOVERY_STATUS_AWAITING_IMAGE,
        0u,
        0u,
        0u
    },
    {
        STATUS_OWNERSHIP_DEVICE_STATUS_RECOVERY_PENDING,
        STATUS_OWNERSHIP_REC_REASON_FLASHLESS_BOOT,
        STATUS_OWNERSHIP_RECOVERY_STATUS_BOOTING_IMAGE,
        2u,
        0xA5u,
        0u
    },
    {
        STATUS_OWNERSHIP_DEVICE_STATUS_RUNNING_RECOVERY,
        STATUS_OWNERSHIP_REC_REASON_NONE,
        STATUS_OWNERSHIP_RECOVERY_STATUS_SUCCESS,
        3u,
        0x5Au,
        0u
    },
    {
        STATUS_OWNERSHIP_DEVICE_STATUS_BOOT_FAILURE,
        STATUS_OWNERSHIP_REC_REASON_AUTH_RECOVERY_FW,
        STATUS_OWNERSHIP_RECOVERY_STATUS_AUTH_ERROR,
        4u,
        0x3Cu,
        0u
    },
    {
        STATUS_OWNERSHIP_DEVICE_STATUS_FATAL_ERROR,
        STATUS_OWNERSHIP_REC_REASON_NONE,
        STATUS_OWNERSHIP_RECOVERY_STATUS_FAILED,
        5u,
        0xC3u,
        STATUS_OWNERSHIP_HW_STATUS_FATAL_ERR
    }
};

static void status_ownership_fail(const char *message)
{
    VPRINTF(ERROR, "%s\n", message);
    SEND_STDOUT_CTRL(0x1);
    while (1) {
    }
}

static void status_ownership_wait_protocol_error(uint8_t expected)
{
    uint32_t word = 0u;

    for (uint32_t poll = 0u; poll < STATUS_OWNERSHIP_POLL_LIMIT; ++poll) {
        if ((cptra_usb_ocp_recovery_read_device_status_word(&word) == 0u) &&
            ((uint8_t)((word & STATUS_OWNERSHIP_PROT_ERROR_MASK) >>
                STATUS_OWNERSHIP_PROT_ERROR_SHIFT) == expected)) {
            return;
        }
    }
    status_ownership_fail(
        "CPTRA: timed out waiting for protocol-error transition");
}

static uint32_t status_ownership_pack_recovery_status(
    const status_ownership_milestone_t *milestone)
{
    return ((uint32_t)milestone->recovery_status & 0x0Fu)
         | (((uint32_t)milestone->image_index & 0x0Fu) << 4)
         | ((uint32_t)milestone->vendor_status << 8);
}

static void status_ownership_program_and_check_milestone(
    const status_ownership_milestone_t *milestone,
    uint8_t program)
{
    uint32_t device_status_word = 0u;
    uint32_t recovery_status_word = 0u;
    uint32_t hw_status_word = 0u;
    uint32_t expected_device_status =
        (uint32_t)milestone->device_status
        | ((uint32_t)milestone->reason_code << 16);
    uint32_t expected_recovery_status =
        status_ownership_pack_recovery_status(milestone);

    if (program != 0u) {
        if (cptra_usb_ocp_recovery_write_device_status(
                milestone->device_status, milestone->reason_code) != 0u
            || cptra_usb_ocp_recovery_write_recovery_status(
                milestone->recovery_status,
                milestone->image_index,
                milestone->vendor_status) != 0u
            || cptra_usb_ocp_recovery_write_hw_status(
                milestone->hw_status) != 0u) {
            status_ownership_fail(
                "CPTRA: firmware-owned status write failed");
        }
    }

    if (cptra_usb_ocp_recovery_read_device_status_word(
            &device_status_word) != 0u
        || cptra_usb_ocp_recovery_read_recovery_status(
            &recovery_status_word) != 0u
        || cptra_usb_ocp_recovery_read_hw_status(
            &hw_status_word) != 0u) {
        status_ownership_fail(
            "CPTRA: firmware-owned status readback failed");
    }

    if ((device_status_word & STATUS_OWNERSHIP_STORAGE_MASK) !=
            expected_device_status
        || recovery_status_word != expected_recovery_status
        || hw_status_word != milestone->hw_status) {
        status_ownership_fail(
            "CPTRA: firmware-owned status readback mismatch");
    }
}

void main(void)
{
    soc_ifc_set_flow_status_field(
        SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) &
            MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 0u) {
    }
    lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, (uint32_t)CMD_COMPLETE);

    for (uint16_t generation = 1u;
         generation <=
            (sizeof(status_ownership_milestones) /
             sizeof(status_ownership_milestones[0]));
         ++generation) {
        const status_ownership_milestone_t *milestone =
            &status_ownership_milestones[generation - 1u];

        status_ownership_program_and_check_milestone(milestone, 1u);
        cptra_usb_ocp_recovery_signal_state_generation(
            STATUS_OWNERSHIP_STATE_READY, 0u, generation);

        status_ownership_wait_protocol_error(1u);
        status_ownership_program_and_check_milestone(milestone, 0u);
        cptra_usb_ocp_recovery_signal_state_generation(
            STATUS_OWNERSHIP_STATE_PROTECTED, 1u, generation);

        status_ownership_wait_protocol_error(0u);
    }

    cptra_usb_ocp_recovery_signal_state_generation(
        STATUS_OWNERSHIP_STATE_DONE, 0u,
        (uint16_t)(sizeof(status_ownership_milestones) /
                   sizeof(status_ownership_milestones[0])));
    while (1) {
    }
}
