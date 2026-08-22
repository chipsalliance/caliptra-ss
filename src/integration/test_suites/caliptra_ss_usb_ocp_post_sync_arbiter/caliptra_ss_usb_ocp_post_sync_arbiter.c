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
#include "mci.h"
#include "printf.h"
#include "soc_address_map.h"
#include "soc_ifc.h"
#define USB_EVENT_LOOP_DIAG_PERIOD 0u
#include "usb.h"
#include "usb_ocp_recovery.h"

#define COMMAND_COMPLETION_ITERATION_LIMIT 1000000u
#define RESET_COMPLETION_ITERATION_LIMIT 20000u

volatile char *stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

static uint8_t generation_is_newer(uint16_t generation,
                                   uint16_t previous_generation)
{
    uint16_t distance = (uint16_t)(generation - previous_generation);

    // RFC 1982 serial arithmetic accepts wrap and rejects duplicate or stale
    // generations within half of the 16-bit serial-number space.
    return (distance != 0u) && (distance < 0x8000u);
}

static uint32_t make_command_ack(uint8_t opcode,
                                 uint8_t expected_delta,
                                 uint16_t generation)
{
    return ((uint32_t)USB_LEGACY_EP0_COMMAND_ACK_MAGIC <<
            USB_LEGACY_EP0_COMMAND_MAGIC_SHIFT) |
           (((uint32_t)opcode & USB_LEGACY_EP0_COMMAND_NIBBLE_MASK) <<
            USB_LEGACY_EP0_COMMAND_OPCODE_SHIFT) |
           (((uint32_t)expected_delta &
             USB_LEGACY_EP0_COMMAND_NIBBLE_MASK) <<
            USB_LEGACY_EP0_COMMAND_DELTA_SHIFT) |
           generation;
}

static void acknowledge_sampled_command(uint32_t command,
                                        uint8_t opcode,
                                        uint8_t expected_delta,
                                        uint16_t generation)
{
    lsu_write_32(SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1,
                 make_command_ack(opcode, expected_delta, generation));

    // The host holds the command until this acknowledgement. Waiting for its
    // release prevents snapshot headers from overwriting the acknowledgement.
    for (uint32_t iteration = 0u;
         iteration < COMMAND_COMPLETION_ITERATION_LIMIT;
         ++iteration) {
        usb_event_loop(1u, 0u);
        if (lsu_read_32(SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_1) !=
            command) {
            return;
        }
    }
    handle_error("MCU: observer command release timed out\n");
}

uint8_t main(void)
{
    uint16_t last_generation = 0u;
    uint16_t baseline_generation = 0u;
    uint32_t baseline_dispatch_count = 0u;
    uint32_t baseline_bus_reset_count = 0u;
    uint8_t baseline_valid = 0u;

    boot_mcu();
    boot_usb_core(usb_ocp_recovery_get_v1p1_config_descriptor,
                  usb_ocp_recovery_handle_class_request);
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();

    while (!mcu_cptra_mb_ready_nb() || !usb_is_configured()) {
        usb_event_loop(1u, 0u);
    }
    while (1) {
        uint32_t command;
        uint8_t magic;
        uint8_t opcode;
        uint8_t expected_delta;
        uint16_t generation;

        usb_event_loop(1u, 0u);
        command = lsu_read_32(SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_1);
        magic = (uint8_t)(command >> USB_LEGACY_EP0_COMMAND_MAGIC_SHIFT);
        if (magic != USB_LEGACY_EP0_COMMAND_MAGIC) {
            continue;
        }
        opcode = (uint8_t)((command >>
            USB_LEGACY_EP0_COMMAND_OPCODE_SHIFT) &
            USB_LEGACY_EP0_COMMAND_NIBBLE_MASK);
        expected_delta = (uint8_t)((command >>
            USB_LEGACY_EP0_COMMAND_DELTA_SHIFT) &
            USB_LEGACY_EP0_COMMAND_NIBBLE_MASK);
        generation = (uint16_t)(command &
            USB_LEGACY_EP0_COMMAND_GENERATION_MASK);
        if ((opcode != USB_LEGACY_EP0_COMMAND_RELEASE_CALIPTRA) ||
            (expected_delta != 0u) ||
            !generation_is_newer(generation, last_generation)) {
            continue;
        }

        acknowledge_sampled_command(
            command, opcode, expected_delta, generation);
        last_generation = generation;
        break;
    }
    caliptra_mailbox_send_ri_download_firmware();

    while (1) {
        uint32_t command;
        uint8_t magic;
        uint8_t opcode;
        uint8_t expected_delta;
        uint16_t generation;

        usb_event_loop(1u, 0u);
        command = lsu_read_32(SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_1);
        magic = (uint8_t)(command >> USB_LEGACY_EP0_COMMAND_MAGIC_SHIFT);
        if (magic != USB_LEGACY_EP0_COMMAND_MAGIC) {
            continue;
        }

        opcode = (uint8_t)((command >>
            USB_LEGACY_EP0_COMMAND_OPCODE_SHIFT) &
            USB_LEGACY_EP0_COMMAND_NIBBLE_MASK);
        expected_delta = (uint8_t)((command >>
            USB_LEGACY_EP0_COMMAND_DELTA_SHIFT) &
            USB_LEGACY_EP0_COMMAND_NIBBLE_MASK);
        generation = (uint16_t)(command &
            USB_LEGACY_EP0_COMMAND_GENERATION_MASK);

        if (opcode == USB_LEGACY_EP0_COMMAND_PUBLISH_BASELINE) {
            if (!generation_is_newer(generation, last_generation)) {
                continue;
            }
            if (expected_delta != 0u) {
                handle_error("MCU: baseline command has nonzero delta\n");
            }

            acknowledge_sampled_command(
                command, opcode, expected_delta, generation);
            baseline_dispatch_count =
                usb_legacy_ep0_get_setup_dispatch_count();
            baseline_bus_reset_count =
                usb_legacy_ep0_get_bus_reset_count();
            baseline_generation = generation;
            baseline_valid = 1u;
            last_generation = generation;
            usb_legacy_ep0_publish_baseline(generation);
            continue;
        }

        if (opcode == USB_LEGACY_EP0_COMMAND_PUBLISH_POST) {
            uint32_t target_dispatch_count;
            uint8_t target_seen = 0u;

            if ((baseline_valid == 0u) ||
                (generation != baseline_generation)) {
                continue;
            }
            if (expected_delta > 1u) {
                handle_error("MCU: unsupported legacy dispatch delta\n");
            }

            acknowledge_sampled_command(
                command, opcode, expected_delta, generation);
            target_dispatch_count =
                baseline_dispatch_count + expected_delta;
            for (uint32_t iteration = 0u;
                 iteration < COMMAND_COMPLETION_ITERATION_LIMIT;
                 ++iteration) {
                usb_event_loop(1u, 0u);
                if (usb_legacy_ep0_get_setup_dispatch_count() ==
                    target_dispatch_count) {
                    target_seen = 1u;
                    break;
                }
            }
            if (target_seen == 0u) {
                handle_error("MCU: legacy dispatch completion timed out\n");
            }

            baseline_valid = 0u;
            usb_legacy_ep0_publish_post_snapshot(generation);
            continue;
        }

        if (opcode == USB_LEGACY_EP0_COMMAND_PUBLISH_RESET_POST) {
            uint8_t target_seen = 0u;

            if ((baseline_valid == 0u) ||
                (generation != baseline_generation) ||
                (expected_delta != 1u)) {
                continue;
            }

            acknowledge_sampled_command(
                command, opcode, expected_delta, generation);
            for (uint32_t iteration = 0u;
                 iteration < RESET_COMPLETION_ITERATION_LIMIT;
                 ++iteration) {
                usb_event_loop(1u, 0u);
                if (usb_legacy_ep0_get_bus_reset_count() >
                    baseline_bus_reset_count) {
                    target_seen = 1u;
                    break;
                }
            }
            if (target_seen == 0u) {
                handle_error("MCU: USB bus-reset completion timed out\n");
            }

            baseline_valid = 0u;
            usb_legacy_ep0_publish_post_snapshot(generation);
        }
    }
}
