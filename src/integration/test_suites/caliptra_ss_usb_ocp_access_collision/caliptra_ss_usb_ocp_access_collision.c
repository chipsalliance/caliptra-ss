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
#include "soc_address_map.h"
#include "soc_ifc.h"
#include "usb.h"
#include "usb_ocp_recovery.h"

// Uses the existing TB/MCU generic-wire command channel.
#define COLLISION_START 8u
#define COLLISION_STOP 9u
#define COLLISION_CMD_LIMIT 2000000u
#define COLLISION_BURST_WORDS 16u
#define COLLISION_SCENARIOS 4u
#define COLLISION_CTRL_SCENARIO 2u
#define COLLISION_WRITE_SCENARIO_MASK 1u
// OCP Recovery v1.1 Sec 9.2: CMS 0, image from CMS, activation disabled.
#define COLLISION_CTRL_WORD 0x00000100u

volatile char *stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

static void ack_command(uint32_t command)
{
    lsu_write_32(SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1,
        ((uint32_t)USB_LEGACY_EP0_COMMAND_ACK_MAGIC <<
         USB_LEGACY_EP0_COMMAND_MAGIC_SHIFT) | (command & 0x00FFFFFFu));
}

uint8_t main(void)
{
    uint32_t last_command = 0u;
    uint32_t active = 0u;
    uint32_t scenario_id = 0u;
    uint32_t prot_cap = 0u;
    uint32_t iteration = 0u;
    uint32_t address = 0u;
    uint32_t value = 0u;

    if (!usb_ocp_recovery_program_device_id() ||
        !usb_ocp_recovery_apply_capability_policy()) {
        handle_error("MCU: collision test Recovery initialization failed\n");
    }
    mcu_cptra_init_d(
        .cfg_cptra_fuse=true, .cfg_cptra_wdt=true, .cptra_wdt_cfg_0=1u,
        .cfg_boot_usb_core=true,
        .usb_config_desc_fn=usb_ocp_recovery_get_v1p1_config_descriptor,
        .usb_class_req_fn=usb_ocp_recovery_handle_class_request);
    mcu_cptra_user_init();
    while (!mcu_cptra_mb_ready_nb() || !usb_is_configured()) {
        usb_event_loop(1u, 0u);
    }
    prot_cap = lsu_read_32(SOC_USB_COMBO_RECOVERY_PROT_CAP_2);

    for (iteration = 0u; iteration < COLLISION_CMD_LIMIT; ++iteration) {
        uint32_t command;
        uint32_t opcode;
        if (last_command == 0u) {
            // Descriptor discovery still needs legacy service until START.
            usb_event_loop(1u, 0u);
        }
        command = lsu_read_32(SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_1);
        if ((command >> USB_LEGACY_EP0_COMMAND_MAGIC_SHIFT) == USB_LEGACY_EP0_COMMAND_MAGIC &&
            command != last_command) {
            opcode = (command >> USB_LEGACY_EP0_COMMAND_OPCODE_SHIFT) &
                     USB_LEGACY_EP0_COMMAND_NIBBLE_MASK;
            if (opcode == COLLISION_START && !active) {
                scenario_id = (command >> USB_LEGACY_EP0_COMMAND_DELTA_SHIFT) &
                              USB_LEGACY_EP0_COMMAND_NIBBLE_MASK;
                if (scenario_id >= COLLISION_SCENARIOS) {
                    handle_error("MCU: invalid collision scenario\n");
                }
                address = scenario_id < COLLISION_CTRL_SCENARIO ?  SOC_USB_COMBO_RECOVERY_PROT_CAP_2 :
                                                                   SOC_USB_COMBO_RECOVERY_RECOVERY_CTRL;
                value = scenario_id < COLLISION_CTRL_SCENARIO ?  prot_cap :
                                                                 COLLISION_CTRL_WORD;
                active = 1u;
            } else if (opcode == COLLISION_STOP && active) {
                active = 0u;
            } else {
                handle_error("MCU: invalid collision command transition\n");
            }
            last_command = command;
            ack_command(command);
            if (opcode == COLLISION_STOP && scenario_id == COLLISION_SCENARIOS - 1u) {
                // No new AXI polling can race the UVM end-of-test drain.
                while (1);
            }
            iteration = 0u;
        }
        if (active) {
            for (uint32_t beat = 0u; beat < COLLISION_BURST_WORDS; ++beat) {
                if (scenario_id & COLLISION_WRITE_SCENARIO_MASK) {
                    lsu_write_32(address, value);
                } else {
                    uint32_t data = lsu_read_32(address);
                    if (scenario_id < COLLISION_CTRL_SCENARIO && data != prot_cap) {
                        handle_error("MCU: PROT_CAP changed during collision test\n");
                    }
                }
                // Sweep instruction delays to avoid fixed bus/link phase lock.
                for (uint32_t delay = 0u; delay < ((beat + iteration) & 7u);
                     ++delay) {
                    __asm__ volatile ("nop");
                }
            }
        }
    }
    handle_error("MCU: collision command/stress loop timed out\n");
    while (1);
}
