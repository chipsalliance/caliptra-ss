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

// Validation-only Caliptra core firmware for firmware-originated protocol errors.
// Hardware owns claimed SETUP servicing. Firmware waits for the FIFO batch
// abort indication, requests OCP_PROTOCOL_ERROR_GENERAL through CALIPTRA_CTRL,
// and confirms EXT reads of DEVICE_STATUS.PROT_ERROR are non-destructive.

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

#define FW_PROTOCOL_ERROR_STATE_READY               0x51u
#define FW_PROTOCOL_ERROR_STATE_BATCH_ABORTED_SEEN  0x52u
#define FW_PROTOCOL_ERROR_STATE_GENERAL_REQ_SENT    0x53u
#define FW_PROTOCOL_ERROR_STATE_PROT_ERROR_STABLE   0x54u
#define FW_PROTOCOL_ERROR_STATE_DONE                0x55u

#define FW_ERROR_MAILBOX_POLL_LIMIT 1000000u
#define FW_ERROR_POLL_LIMIT 200000u

static void fw_error_fail_and_halt(const char *message)
{
    VPRINTF(ERROR, "%s\n", message);
    SEND_STDOUT_CTRL(0x1);
    while (1) {
    }
}

static void fw_error_wait_for_mailbox_release(void)
{
    for (uint32_t poll = 0u; poll < FW_ERROR_MAILBOX_POLL_LIMIT; ++poll) {
        if (lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) &
            MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) {
            lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, (uint32_t)CMD_COMPLETE);
            return;
        }
    }
    fw_error_fail_and_halt("CPTRA: mailbox release timed out");
}

static void fw_error_wait_for_batch_aborted(void)
{
    uint8_t batch_aborted = 0u;

    for (uint32_t poll = 0u; poll < FW_ERROR_POLL_LIMIT; ++poll) {
        if ((cptra_usb_ocp_recovery_read_batch_aborted(&batch_aborted) == 0u) &&
            (batch_aborted != 0u)) {
            return;
        }
    }
    fw_error_fail_and_halt("CPTRA: CALIPTRA_STATUS.BATCH_ABORTED not observed");
}

static uint8_t fw_error_read_path_disable_state(void)
{
    uint8_t disabled = 0u;

    if (cptra_usb_ocp_recovery_read_path_disable(&disabled) != 0u) {
        fw_error_fail_and_halt("CPTRA: CALIPTRA_CTRL.OCP_PATH_DISABLE read failed");
    }
    return disabled;
}

static void fw_error_wait_for_general_request_clear(uint8_t expected_path_disable)
{
    uint32_t ctrl_word = 0u;
    uint32_t expected_path_disable_mask =
        expected_path_disable != 0u ?
        USB_OCP_RECOVERY_REG_CALIPTRA_CTRL_OCP_PATH_DISABLE_MASK : 0u;

    for (uint32_t poll = 0u; poll < FW_ERROR_POLL_LIMIT; ++poll) {
        if (cptra_usb_ocp_recovery_read_caliptra_ctrl(&ctrl_word) != 0u) {
            continue;
        }
        if ((ctrl_word &
             USB_OCP_RECOVERY_REG_CALIPTRA_CTRL_OCP_PATH_DISABLE_MASK) !=
            expected_path_disable_mask) {
            fw_error_fail_and_halt(
                "CPTRA: OCP_PATH_DISABLE changed during general-error request");
        }
        if ((ctrl_word &
             USB_OCP_RECOVERY_REG_CALIPTRA_CTRL_OCP_PROTOCOL_ERROR_GENERAL_MASK)
            == 0u) {
            return;
        }
    }
    fw_error_fail_and_halt(
        "CPTRA: OCP_PROTOCOL_ERROR_GENERAL request did not self-clear");
}

static uint8_t fw_error_wait_for_general_protocol_error(void)
{
    uint8_t prot_error = 0u;

    for (uint32_t poll = 0u; poll < FW_ERROR_POLL_LIMIT; ++poll) {
        if (cptra_usb_ocp_recovery_read_device_status_prot_error(
                &prot_error) != 0u) {
            continue;
        }
        if (prot_error == CPTRA_USB_OCP_RECOVERY_PROTOCOL_ERROR_GENERAL) {
            return prot_error;
        }
    }
    fw_error_fail_and_halt(
        "CPTRA: DEVICE_STATUS.PROT_ERROR did not reach GENERAL");
    return 0u;
}

void main(void)
{
    uint8_t path_disable = 0u;
    uint8_t prot_error = 0u;
    uint8_t result = 0u;

    VPRINTF(LOW, "CPTRA: Firmware protocol-error validation firmware start\n");

    soc_ifc_set_flow_status_field(
        SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);
    fw_error_wait_for_mailbox_release();
    cptra_usb_ocp_recovery_signal_state_generation(
        CPTRA_USB_OCP_FW_STATE_PATH_READY, 0u, 0u);

    cptra_usb_ocp_recovery_signal_state(FW_PROTOCOL_ERROR_STATE_READY, 0u);

    fw_error_wait_for_batch_aborted();
    path_disable = fw_error_read_path_disable_state();
    cptra_usb_ocp_recovery_signal_state(
        FW_PROTOCOL_ERROR_STATE_BATCH_ABORTED_SEEN, path_disable);

    result = cptra_usb_ocp_recovery_request_general_protocol_error();
    if (result == 1u) {
        fw_error_fail_and_halt(
            "CPTRA: general protocol-error request register access failed");
    }
    if (result == 2u) {
        fw_error_fail_and_halt(
            "CPTRA: general protocol-error request issued before batch abort");
    }
    if (result == 3u) {
        fw_error_fail_and_halt(
            "CPTRA: OCP_CLAIM_ABORT still observed during general-error request");
    }
    cptra_usb_ocp_recovery_signal_state(
        FW_PROTOCOL_ERROR_STATE_GENERAL_REQ_SENT, path_disable);

    fw_error_wait_for_general_request_clear(path_disable);

    prot_error = fw_error_wait_for_general_protocol_error();
    result = cptra_usb_ocp_recovery_verify_device_status_prot_error_stable(
        &prot_error);
    if (result == 1u) {
        fw_error_fail_and_halt(
            "CPTRA: DEVICE_STATUS.PROT_ERROR stability reads failed");
    }
    if (result == 2u) {
        fw_error_fail_and_halt(
            "CPTRA: DEVICE_STATUS.PROT_ERROR changed across EXT reads");
    }
    if (prot_error != CPTRA_USB_OCP_RECOVERY_PROTOCOL_ERROR_GENERAL) {
        fw_error_fail_and_halt(
            "CPTRA: DEVICE_STATUS.PROT_ERROR unexpected after stable reads");
    }
    cptra_usb_ocp_recovery_signal_state(
        FW_PROTOCOL_ERROR_STATE_PROT_ERROR_STABLE, prot_error);

    VPRINTF(LOW,
            "CPTRA: Firmware protocol-error validation observed PROT_ERROR=0x%02x\n",
            prot_error);
    cptra_usb_ocp_recovery_signal_state(FW_PROTOCOL_ERROR_STATE_DONE, prot_error);

    while (1) {
    }
}
