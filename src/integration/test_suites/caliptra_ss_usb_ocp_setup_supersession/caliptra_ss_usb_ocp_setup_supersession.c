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

// Test-local extensions of the observer command protocol in usb.h.
#define CMD_ARM       0xAu
#define CMD_RELEASE   0xBu
#define CMD_STALE     0xCu
#define CMD_EXPOSE    0xDu
#define CMD_NEXT      0xEu
#define CMD_FIFO_DRAIN 0xFu
#define STATE_READY   1u
#define STATE_HELD    2u
#define STATE_RELEASED 3u
#define STATE_STALE   4u
#define PROGRESS_MAGIC 0xE1u
#define POLL_LIMIT    100000u
// Same 18-field wire layout; test-local field 11 is the notified-work count,
// fields 14/15 are ordinary OUT/IN completions, and field 16 is dispatch delta.
#define SUPERSESSION_SNAPSHOT_VERSION 2u
#define SCENARIO_SHORT_SETUP 7u
#define SCENARIO_BAD_CRC_SETUP 8u
#define SCENARIO_LAST 15u

static uint16_t scenario_generation;
static uint8_t scenario;
static uint8_t responder_state;
static uint8_t held;
static uint8_t expect_new_setup;
static uint32_t notifications;
static uint32_t ordinary_out;
static uint32_t ordinary_in;
static uint32_t dispatch_baseline;
static uint32_t publish_sequence;

// A valid device descriptor with deliberately different identity bytes. It is
// published by an obsolete handler, not by normal GET_DESCRIPTOR dispatch.
static const uint32_t old_descriptor[5] = {
    0x02000112u, 0x400101FFu, 0xA65AC35Au, 0x02015678u, 0x00000103u
};

static void progress(void)
{
    lsu_write_32(SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_0,
                 (notifications << 16) |
                 (usb_legacy_ep0_get_setup_dispatch_count() - dispatch_baseline));
    lsu_write_32(SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1,
                 (PROGRESS_MAGIC << 24) | ((uint32_t)responder_state << 20) |
                 ((uint32_t)scenario << 16) | scenario_generation);
}

static void wait_input(uint32_t address, uint32_t value)
{
    for (uint32_t i = 0; i < POLL_LIMIT; ++i) {
        if (lsu_read_32(address) == value) {
            return;
        }
    }
    handle_error("MCU: supersession snapshot ACK timed out\n");
}

static void wait_command_release(uint32_t command)
{
    for (uint32_t i = 0; i < POLL_LIMIT; ++i) {
        if (lsu_read_32(SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_1) != command) {
            return;
        }
    }
    handle_error("MCU: supersession command release timed out\n");
}

static void publish_snapshot(uint16_t generation, uint32_t snapshot_state)
{
    usb_legacy_ep0_snapshot_t snapshot;
    uint32_t fields[USB_LEGACY_EP0_SNAPSHOT_FIELDS];
    usb_legacy_ep0_capture_snapshot(&snapshot);
    // The dedicated responder owns interrupt accounting after enumeration.
    fields[0] = ++publish_sequence;
    fields[1] = snapshot.setup_word0;
    fields[2] = snapshot.setup_word1;
    fields[3] = snapshot.ep0_out_descriptor;
    fields[4] = snapshot.ep0_setup_descriptor;
    fields[5] = snapshot.ep0_in_descriptor;
    fields[6] = snapshot.ep0_reserved_descriptor;
    fields[7] = snapshot.devcmdstat;
    fields[8] = snapshot.intstat;
    fields[9] = snapshot.inten;
    fields[10] = snapshot.configuration;
    fields[11] = notifications;
    fields[12] = snapshot.bus_reset_count;
    fields[13] = ordinary_out + ordinary_in + notifications;
    fields[14] = ordinary_out;
    fields[15] = ordinary_in;
    fields[16] = usb_legacy_ep0_get_setup_dispatch_count() - dispatch_baseline;
    fields[17] = SUPERSESSION_SNAPSHOT_VERSION;
    for (uint32_t i = 0; i < USB_LEGACY_EP0_SNAPSHOT_FIELDS; ++i) {
        uint32_t header = (USB_LEGACY_EP0_DATA_MAGIC << 24) |
                          (snapshot_state << 22) | (i << 17) | generation;
        lsu_write_32(SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_0, fields[i]);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1, header);
        wait_input(SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_0,
                   (header & 0x00FFFFFFu) | (USB_LEGACY_EP0_ACK_MAGIC << 24));
        lsu_write_32(SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1, 0u);
        wait_input(SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_0, 0u);
    }
    lsu_write_32(SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1,
                 (USB_LEGACY_EP0_READY_MAGIC << 24) |
                 (snapshot_state << 22) | (USB_LEGACY_EP0_READY_FIELD << 17) |
                 generation);
}

static void service_ep0(void)
{
    uint32_t irq = lsu_read_32(USB_DEV_INTSTAT);
    if ((irq & DEV0_CSR_INTSTAT_EP0IN_MASK) != 0u) {
        lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);
        ++ordinary_in;
    }
    if ((irq & DEV0_CSR_INTSTAT_EP0OUT_MASK) != 0u) {
        lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0OUT_MASK);
        // Only a freshly consumed EP0 OUT notification authorizes inspecting
        // SETUP. A second notification in this epoch is DATA/STATUS, not a new
        // dispatch opportunity. ARM drains old sticky state before host work.
        if ((scenario == SCENARIO_SHORT_SETUP) ||
            (scenario == SCENARIO_BAD_CRC_SETUP)) {
            // Dedicated characterization epochs have no firmware dispatch.
            // Record whatever the hardware actually notifies; do not require
            // malformed-frame IRQ suppression or discover work from SETUP
            // polling. A SETUP level without EP0OUT notification is untouched.
            if ((lsu_read_32(USB_DEV_DEVCMDSTAT) &
                 DEV0_CSR_DEVCMDSTAT_SETUP_MASK) != 0u) {
                ++notifications;
            } else {
                ++ordinary_out;
            }
        } else if (expect_new_setup &&
            ((lsu_read_32(USB_DEV_DEVCMDSTAT) &
              DEV0_CSR_DEVCMDSTAT_SETUP_MASK) != 0u)) {
            usb_setup_pkt_t setup;
            usb_read_setup_packet(&setup);
            if ((setup.bmRequestType != 0x80u) ||
                (setup.bRequest != USB_REQ_GET_DESCRIPTOR) ||
                (setup.wValue != 0x0100u) || (setup.wIndex != 0u) ||
                ((setup.wLength != 18u) && (setup.wLength != 8u))) {
                handle_error("MCU: unexpected notified SETUP in supersession epoch\n");
            }
            ++notifications;
            expect_new_setup = 0u;
            held = 1u;
            responder_state = STATE_HELD;
            progress();
        } else {
            ++ordinary_out;
        }
    }
}

static void drain_diagnostic_fifo(void)
{
    uint32_t words = lsu_read_32(SOC_USB_COMBO_RECOVERY_INDIRECT_FIFO_CTRL_1);
    if ((words == 0u) || (words > POLL_LIMIT)) {
        handle_error("MCU: invalid diagnostic FIFO drain length\n");
    }
    // The host wrote this complete image using runtime-discovered limits.
    // No implicit consumer runs while AXI checks the diagnostic RO words.
    for (uint32_t i = 0; i < words; ++i) {
        if ((lsu_read_32(SOC_USB_COMBO_RECOVERY_INDIRECT_FIFO_STATUS_0) &
             RECOVERY_INDIRECT_FIFO_STATUS_0_EMPTY_MASK) != 0u) {
            handle_error("MCU: diagnostic reads consumed FIFO data\n");
        }
        if (lsu_read_32(SOC_USB_COMBO_RECOVERY_INDIRECT_FIFO_DATA) !=
            (0x53540000u | i)) {
            handle_error("MCU: diagnostic FIFO payload mismatch\n");
        }
    }
    if ((lsu_read_32(SOC_USB_COMBO_RECOVERY_INDIRECT_FIFO_STATUS_0) &
         RECOVERY_INDIRECT_FIFO_STATUS_0_EMPTY_MASK) == 0u) {
        handle_error("MCU: diagnostic FIFO did not empty after exact drain\n");
    }
}

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
    // Linking usb_ocp_recovery.o supplies strong usb_get_config_descriptor()
    // and usb_handle_class_request() overrides; boot takes no hook arguments.
    mcu_cptra_init_d(
        .cfg_cptra_fuse=true,
        .cfg_cptra_wdt=true,
        .cptra_wdt_cfg_0=1u,
        .cfg_boot_usb_core=true);
    mcu_cptra_user_init();

    VPRINTF(LOW, "MCU: USB OCP SETUP supersession responder ready\n");

    while (!usb_is_configured()) {
        usb_event_loop(1u, 0u);
    }
    // Keep the responder available for back-to-back requests rather than
    // spending several microseconds printing each completed SETUP handler.
    verbosity_g = ERROR;

    uint16_t last_generation = 0u;
    uint8_t publish_pending = 0u;
    uint16_t publish_generation = 0u;
    uint32_t publish_state = 0u;
    while (1) {
        uint32_t command;
        uint8_t magic;
        uint8_t opcode;
        uint8_t expected_delta;
        uint16_t generation;
        uint32_t acknowledgement;

        // After the first ARM, barriers hold notified legacy work without
        // discovering OCP work from SETUP level.
        if (scenario_generation == 0u) {
            // Runtime functional-descriptor discovery follows configuration;
            // the first ARM, not SET_CONFIGURATION, ends normal USB service.
            usb_event_loop(1u, 0u);
        } else {
            service_ep0();
        }
        command = lsu_read_32(SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_1);
        magic = (uint8_t)(command >> USB_LEGACY_EP0_COMMAND_MAGIC_SHIFT);
        opcode = (uint8_t)((command >>
            USB_LEGACY_EP0_COMMAND_OPCODE_SHIFT) &
            USB_LEGACY_EP0_COMMAND_NIBBLE_MASK);
        if (magic != USB_LEGACY_EP0_COMMAND_MAGIC) {
            continue;
        }

        expected_delta = (uint8_t)((command >>
            USB_LEGACY_EP0_COMMAND_DELTA_SHIFT) &
            USB_LEGACY_EP0_COMMAND_NIBBLE_MASK);
        generation = (uint16_t)(command &
            USB_LEGACY_EP0_COMMAND_GENERATION_MASK);
        if ((generation == 0u) || (generation <= last_generation)) {
            handle_error("MCU: invalid supersession command generation\n");
        }
        last_generation = generation;
        acknowledgement =
            ((uint32_t)USB_LEGACY_EP0_COMMAND_ACK_MAGIC <<
             USB_LEGACY_EP0_COMMAND_MAGIC_SHIFT) |
            ((uint32_t)opcode << USB_LEGACY_EP0_COMMAND_OPCODE_SHIFT) |
            ((uint32_t)expected_delta << USB_LEGACY_EP0_COMMAND_DELTA_SHIFT) |
            generation;

        switch (opcode) {
        case CMD_ARM:
            if (expected_delta > SCENARIO_LAST) {
                handle_error("MCU: invalid supersession scenario\n");
            }
            scenario_generation = generation;
            scenario = expected_delta;
            held = 0u;
            expect_new_setup = 1u;
            notifications = ordinary_out = ordinary_in = 0u;
            dispatch_baseline = usb_legacy_ep0_get_setup_dispatch_count();
            // Host is quiescent at ARM. Do not clear SETUP or descriptors.
            lsu_write_32(USB_DEV_INTSTAT,
                         DEV0_CSR_INTSTAT_EP0OUT_MASK | DEV0_CSR_INTSTAT_EP0IN_MASK);
            if ((lsu_read_32(USB_DEV_INTSTAT) & 3u) != 0u) {
                handle_error("MCU: old EP0 IRQ did not drain before ARM\n");
            }
            responder_state = STATE_READY;
            break;
        case CMD_RELEASE:
        case CMD_EXPOSE:
            if ((expected_delta != 0u) || !held || (responder_state != STATE_HELD)) {
                handle_error("MCU: release without notified held legacy SETUP\n");
            }
            if (opcode == CMD_RELEASE) {
                // This notification-qualified call prepares the current
                // payload and both descriptors before any effective SETUP
                // clear. DEVCMDSTAT RMWs can also echo the W1C SETUP bit;
                // the final explicit helper is not an atomic release lock.
                if (!usb_handle_control_transfer()) {
                    handle_error("MCU: supersession legacy dispatch failed\n");
                }
            } else {
                // Deliberate lifecycle defect characterization: release the
                // *new* SETUP without replacing the obsolete ACTIVE IN entry.
                usb_ep0_arm_out();
                usb_clear_setup_bit();
            }
            held = 0u;
            responder_state = STATE_RELEASED;
            break;
        case CMD_NEXT:
            if ((scenario == SCENARIO_SHORT_SETUP) ||
                (scenario == SCENARIO_BAD_CRC_SETUP) ||
                (notifications != expected_delta)) {
                handle_error("MCU: next request has invalid notification epoch\n");
            }
            // Host is quiescent after the preceding transfer's retirement.
            // Retire its notification credit, not SETUP or response SRAM.
            // Only a subsequent EP0 OUT notification may hold the next work.
            lsu_write_32(USB_DEV_INTSTAT,
                         DEV0_CSR_INTSTAT_EP0OUT_MASK | DEV0_CSR_INTSTAT_EP0IN_MASK);
            if ((lsu_read_32(USB_DEV_INTSTAT) & 3u) != 0u) {
                handle_error("MCU: old EP0 IRQ did not drain before next request\n");
            }
            scenario_generation = generation;
            held = 0u;
            expect_new_setup = 1u;
            responder_state = STATE_READY;
            break;
        case CMD_STALE:
            if ((scenario != 4u) || (expected_delta != 0u) ||
                !held || (responder_state != STATE_HELD)) {
                handle_error("MCU: stale publish without obsolete held handler\n");
            }
            usb_ep0_send_data(old_descriptor, 18u);
            // Do not clear SETUP: this response belongs to the superseded work.
            responder_state = STATE_STALE;
            break;
        case CMD_FIFO_DRAIN:
            if ((expected_delta != 0u) || held ||
                (scenario == SCENARIO_SHORT_SETUP) ||
                (scenario == SCENARIO_BAD_CRC_SETUP)) {
                handle_error("MCU: invalid diagnostic FIFO drain command\n");
            }
            drain_diagnostic_fifo();
            break;
        case USB_LEGACY_EP0_COMMAND_PUBLISH_BASELINE:
        case USB_LEGACY_EP0_COMMAND_PUBLISH_POST:
            if ((opcode == USB_LEGACY_EP0_COMMAND_PUBLISH_POST) &&
                ((usb_legacy_ep0_get_setup_dispatch_count() - dispatch_baseline) !=
                 expected_delta)) {
                handle_error("MCU: supersession dispatch count mismatch\n");
            }
            publish_pending = 1u;
            publish_generation = generation;
            publish_state = (opcode == USB_LEGACY_EP0_COMMAND_PUBLISH_BASELINE) ?
                            USB_LEGACY_EP0_SNAPSHOT_BASELINE :
                            USB_LEGACY_EP0_SNAPSHOT_POST;
            break;
        case USB_LEGACY_EP0_COMMAND_STOP:
            if (expected_delta != 0u) {
                handle_error("MCU: invalid supersession STOP command\n");
            }
            // STOP ACK is the final MMIO: no release polling or USB service.
            csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);
            __asm__ volatile ("fence iorw, iorw" ::: "memory");
            lsu_write_32(SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1,
                         acknowledgement);
            __asm__ volatile ("fence iorw, iorw" ::: "memory");
            while (1) {
                csr_write_mpmc(STOP_MPMC_HALT);
            }
        default:
            handle_error("MCU: unknown supersession command\n");
        }
        __asm__ volatile ("fence iorw, iorw" ::: "memory");
        lsu_write_32(SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1,
                     acknowledgement);
        // Hold ACK until command withdrawal; the host can never miss a pulse.
        wait_command_release(command);
        if (publish_pending) {
            publish_pending = 0u;
            publish_snapshot(publish_generation, publish_state);
        } else {
            progress();
        }
    }
}
