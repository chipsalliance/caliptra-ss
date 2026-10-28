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

#include "caliptra_ss_lib.h"
#include "printf.h"
#include "riscv-csr.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"
#include "usb.h"
#include "usb_ocp_recovery.h"
#include "veer-csr.h"

// MPMC[0] requests halt; leave MPMC[1] clear to keep interrupts masked.
#define STOP_MPMC_HALT 0x1u

volatile char *stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

uint8_t main(void)
{
    VPRINTF(LOW, "MCU: USB OCP SETUP supersession responder starting\n");

    if (!usb_ocp_recovery_program_device_id()) {
        handle_error("MCU: Failed to program USB Recovery DEVICE_ID\n");
    }
    if (!usb_ocp_recovery_apply_capability_policy()) {
        handle_error("MCU: Failed to apply USB Recovery capability policy\n");
    }
    mcu_cptra_init_d(
        .cfg_cptra_fuse=true,
        .cfg_cptra_wdt=true,
        .cptra_wdt_cfg_0=1u,
        .cfg_boot_usb_core=true,
        .usb_config_desc_fn=usb_ocp_recovery_get_v1p1_config_descriptor,
        .usb_class_req_fn=usb_ocp_recovery_handle_class_request);
    mcu_cptra_user_init();

    VPRINTF(LOW, "MCU: USB OCP SETUP supersession responder ready\n");

    while (!usb_is_configured()) {
        usb_event_loop(1u, 0u);
    }
    // Keep the responder available for back-to-back requests rather than
    // spending several microseconds printing each completed SETUP handler.
    verbosity_g = ERROR;

    while (1) {
        uint32_t command;
        uint8_t magic;
        uint8_t opcode;
        uint8_t expected_delta;
        uint16_t generation;
        uint32_t acknowledgement;

        usb_event_loop(1u, 0u);
        command = lsu_read_32(SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_1);
        magic = (uint8_t)(command >> USB_LEGACY_EP0_COMMAND_MAGIC_SHIFT);
        opcode = (uint8_t)((command >>
            USB_LEGACY_EP0_COMMAND_OPCODE_SHIFT) &
            USB_LEGACY_EP0_COMMAND_NIBBLE_MASK);
        if ((magic != USB_LEGACY_EP0_COMMAND_MAGIC) ||
            (opcode != USB_LEGACY_EP0_COMMAND_STOP)) {
            continue;
        }

        expected_delta = (uint8_t)((command >>
            USB_LEGACY_EP0_COMMAND_DELTA_SHIFT) &
            USB_LEGACY_EP0_COMMAND_NIBBLE_MASK);
        generation = (uint16_t)(command &
            USB_LEGACY_EP0_COMMAND_GENERATION_MASK);
        if ((expected_delta != 0u) || (generation == 0u)) {
            handle_error("MCU: invalid supersession STOP command\n");
        }
        acknowledgement =
            ((uint32_t)USB_LEGACY_EP0_COMMAND_ACK_MAGIC <<
             USB_LEGACY_EP0_COMMAND_MAGIC_SHIFT) |
            ((uint32_t)opcode << USB_LEGACY_EP0_COMMAND_OPCODE_SHIFT) |
            ((uint32_t)expected_delta << USB_LEGACY_EP0_COMMAND_DELTA_SHIFT) |
            generation;

        // STOP ACK is the final MMIO: no command-release polling or USB service.
        csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);
        __asm__ volatile ("fence iorw, iorw" ::: "memory");
        lsu_write_32(SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1,
                     acknowledgement);
        __asm__ volatile ("fence iorw, iorw" ::: "memory");
        while (1) {
            csr_write_mpmc(STOP_MPMC_HALT);
        }
    }
}
