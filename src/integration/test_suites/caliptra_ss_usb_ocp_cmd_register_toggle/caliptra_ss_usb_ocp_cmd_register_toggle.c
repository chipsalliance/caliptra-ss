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

#define SWEEP_TARGET_COUNT 6u
#define SWEEP_LOAD_BYTE0 0x60u
#define SWEEP_SELECT 0x64u
#define SWEEP_WRITE 0x65u
#define SWEEP_RESTORE 0x66u
#define SWEEP_POLL_LIMIT 200000u

// OCP Recovery v1.1 Section 9.2, in the same target order as the host.
// These masks select mutable protocol fields, not register reset values.
static const uint64_t addresses[SWEEP_TARGET_COUNT] = {
    SOC_USB_COMBO_RECOVERY_PROT_CAP_2,
    SOC_USB_COMBO_RECOVERY_PROT_CAP_3,
    SOC_USB_COMBO_RECOVERY_RECOVERY_CTRL,
    SOC_USB_COMBO_RECOVERY_RECOVERY_STATUS,
    SOC_USB_COMBO_RECOVERY_DEVICE_STATUS_0,
    SOC_USB_COMBO_RECOVERY_HW_STATUS
};
static const uint32_t masks[SWEEP_TARGET_COUNT] = {
    0x1FFF0000u, 0x00FFFFFFu, 0x000F03FFu, 0x0000FFFFu,
    0x00FF000Fu, 0x00FFFF07u
};

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

static void fail_and_halt(const char *message, uint16_t generation)
{
    VPRINTF(FATAL, "CPTRA: %s\n", message);
    cptra_usb_ocp_recovery_signal_state_generation(
        CPTRA_USB_OCP_FW_STATE_COMMAND_ERROR, 0u, generation);
    SEND_STDOUT_CTRL(0x1);
    while (1) {
    }
}

static uint32_t wait_command(uint16_t generation)
{
    for (uint32_t poll = 0u; poll < SWEEP_POLL_LIMIT; ++poll) {
        uint32_t command = 0u;
        uint32_t magic = 0u;
        cptra_usb_ocp_recovery_read_fw_command(&command, &magic);
        if ((magic == CPTRA_USB_OCP_FW_COMMAND_MAGIC) &&
            ((uint16_t)(command >> 16) == generation)) {
            return command;
        }
        spin_delay();
    }
    fail_and_halt("register-sweep command timed out", generation);
    return 0u;
}

static void wait_release(uint16_t generation)
{
    for (uint32_t poll = 0u; poll < SWEEP_POLL_LIMIT; ++poll) {
        uint32_t command = 0u;
        uint32_t magic = 0u;
        cptra_usb_ocp_recovery_read_fw_command(&command, &magic);
        if (magic != CPTRA_USB_OCP_FW_COMMAND_MAGIC) {
            return;
        }
        spin_delay();
    }
    fail_and_halt("register-sweep command release timed out", generation);
}

static uint32_t read_target(uint8_t target, uint16_t generation)
{
    uint32_t value = 0u;
    if (cptra_usb_ocp_recovery_read_dword_retry(
            addresses[target], &value) != 0u) {
        fail_and_halt("register-sweep CPU read failed", generation);
    }
    return value;
}

static void write_target(uint8_t target, uint32_t value, uint16_t generation)
{
    uint32_t before = read_target(target, generation);
    uint32_t expected = (before & ~masks[target]) | (value & masks[target]);
    uint32_t observed;
    if (cptra_usb_ocp_recovery_write_dword(addresses[target], expected) != 0u) {
        fail_and_halt("register-sweep CPU write failed", generation);
    }
    observed = read_target(target, generation);
    if (((observed ^ expected) & masks[target]) != 0u) {
        VPRINTF(FATAL, "CPTRA: sweep target=%u wrote=0x%08x got=0x%08x mask=0x%08x\n",
                target, expected, observed, masks[target]);
        fail_and_halt("register-sweep CPU readback mismatch", generation);
    }
}

void main(void)
{
    uint16_t generation = 0u;
    uint8_t selected = SWEEP_TARGET_COUNT;
    uint8_t loaded_bytes = 0u;
    uint32_t original = 0u;
    uint32_t pending = 0u;

    soc_ifc_set_flow_status_field(
        SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);
    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) &
            MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 0u) {
        spin_delay();
    }
    lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, (uint32_t)CMD_COMPLETE);
    cptra_usb_ocp_recovery_signal_state_generation(
        CPTRA_USB_OCP_FW_STATE_PATH_READY, 0u, generation);

    while (1) {
        uint32_t command = wait_command(++generation);
        uint8_t opcode = (uint8_t)(command >> 8);
        uint8_t data = (uint8_t)command;
        uint8_t ack_state = CPTRA_USB_OCP_FW_STATE_PATH_READY;
        if (opcode == SWEEP_SELECT) {
            if ((data >= SWEEP_TARGET_COUNT) || (selected != SWEEP_TARGET_COUNT)) {
                fail_and_halt("invalid or unrestored sweep target", generation);
            }
            selected = data;
            original = read_target(selected, generation);
            pending = 0u;
            loaded_bytes = 0u;
        } else if ((opcode >= SWEEP_LOAD_BYTE0) &&
                   (opcode < (SWEEP_LOAD_BYTE0 + 4u)) &&
                   (selected < SWEEP_TARGET_COUNT)) {
            uint32_t shift = (opcode - SWEEP_LOAD_BYTE0) * 8u;
            pending = (pending & ~(0xFFu << shift)) | ((uint32_t)data << shift);
            loaded_bytes |= (uint8_t)(1u << (opcode - SWEEP_LOAD_BYTE0));
        } else if ((opcode == SWEEP_WRITE) && (selected < SWEEP_TARGET_COUNT)) {
            if (loaded_bytes != 0x0Fu) {
                fail_and_halt("incomplete register-sweep value", generation);
            }
            write_target(selected, pending, generation);
            loaded_bytes = 0u;
        } else if ((opcode == SWEEP_RESTORE) && (selected < SWEEP_TARGET_COUNT)) {
            write_target(selected, original, generation);
            VPRINTF(LOW, "CPTRA: register-sweep target %u restored\n", selected);
            selected = SWEEP_TARGET_COUNT;
        } else if ((opcode == CPTRA_USB_OCP_FW_COMMAND_FLOW_COMPLETE) &&
                   (selected == SWEEP_TARGET_COUNT)) {
            ack_state = CPTRA_USB_OCP_FW_STATE_FLOW_COMPLETE;
        } else {
            fail_and_halt("invalid register-sweep command", generation);
        }
        cptra_usb_ocp_recovery_signal_state_generation(ack_state, data, generation);
        wait_release(generation);
        if (ack_state == CPTRA_USB_OCP_FW_STATE_FLOW_COMPLETE) {
            cptra_usb_ocp_recovery_publish_completion();
            while (1) {
            }
        }
        cptra_usb_ocp_recovery_signal_state_generation(
            CPTRA_USB_OCP_FW_STATE_COMMAND_BUSY, 0u, generation);
    }
}
