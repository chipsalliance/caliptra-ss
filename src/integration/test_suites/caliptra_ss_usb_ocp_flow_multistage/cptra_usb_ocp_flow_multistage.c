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

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "flow004.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"
#include "soc_ifc.h"
#include "usb_ocp_recovery_cptra.h"

volatile char *stdout = (char *)STDOUT;
volatile uint32_t intr_count = 0u;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};
enum printf_verbosity verbosity_g = LOW;

static uint32_t image[FLOW004_MAX_WORDS] __attribute__((section(".dccm")));
static flow004_manifest_t manifest;
static uint32_t next_stage;

static void fail(const char *message)
{
    VPRINTF(FATAL, "FLOW004: %s\n", message);
    SEND_STDOUT_CTRL(0x1);
    while (1) {}
}

static void delay(void)
{
    for (uint32_t i = 0u; i < 32u; ++i) {
        __asm__ volatile ("nop");
    }
}

static void publish(uint8_t device, uint8_t recovery, uint8_t stage)
{
    if (cptra_usb_ocp_recovery_write_device_status(device, 0u) ||
        cptra_usb_ocp_recovery_write_recovery_status(recovery, stage, 0u)) {
        fail("status publication failed");
    }
}

static void wait_command(uint8_t expected, uint16_t generation)
{
    for (uint32_t poll = 0u; poll < FLOW004_POLL_LIMIT; ++poll) {
        uint32_t word, magic;
        cptra_usb_ocp_recovery_read_fw_command(&word, &magic);
        if (magic == CPTRA_USB_OCP_FW_COMMAND_MAGIC &&
            (uint16_t)(word >> 16) == generation &&
            (uint8_t)(word >> 8) == expected) {
            return;
        }
        delay();
    }
    fail("host observation handshake timed out");
}

static void receive_stage(uint32_t stage)
{
    uint32_t words, pages;
    uint8_t *payload = (uint8_t *)image + FLOW004_HEADER_BYTES;

    if (stage != next_stage || stage > 2u) {
        fail("downloaded runtime requested stages out of order");
    }
    publish(stage == 0u ? 3u : 5u, 1u, (uint8_t)stage);
    cptra_usb_ocp_recovery_signal_state_generation(
        CPTRA_USB_OCP_FW_STATE_PATH_READY, (uint8_t)stage,
        (uint16_t)(stage + 1u));
    if (cptra_usb_ocp_recovery_wait_payload_available(FLOW004_POLL_LIMIT)) {
        fail("payload_available timed out");
    }
    words = cptra_usb_ocp_recovery_read_image_size_words();
    if (words <= FLOW004_HEADER_BYTES / 4u || words > FLOW004_MAX_WORDS) {
        fail("invalid protocol IMAGE_SIZE");
    }
    if (cptra_usb_ocp_recovery_read_dword_retry(
            SOC_MCI_TOP_MCI_REG_FW_SRAM_EXEC_REGION_SIZE, &pages) ||
        words * 4u >
            (((pages & MCI_REG_FW_SRAM_EXEC_REGION_SIZE_SIZE_MASK) >>
               MCI_REG_FW_SRAM_EXEC_REGION_SIZE_SIZE_LOW) + 1u) * 4096u) {
        fail("image exceeds discovered execution region");
    }
    if (cptra_usb_ocp_recovery_stream_fifo_to_axi(
            SOC_MCI_TOP_MCU_SRAM_BASE_ADDR, words * 4u, 64u) ||
        cptra_usb_ocp_recovery_read_axi_payload(
            SOC_MCI_TOP_MCU_SRAM_BASE_ADDR, image, words * 4u)) {
        fail("image DMA/verification read failed");
    }
    if (image[0] != FLOW004_MAGIC || image[1] != stage ||
        image[2] != words * 4u - FLOW004_HEADER_BYTES ||
        flow004_checksum(payload, image[2]) != image[3]) {
        fail("complete image integrity/identity check failed");
    }
    if (stage == 1u) {
        if (image[2] < sizeof(manifest)) {
            fail("truncated test manifest");
        }
        manifest.magic = image[4];
        manifest.mcu_destination = image[5];
        manifest.mcu_payload_bytes = image[6];
        manifest.mcu_checksum = image[7];
        if (manifest.magic != FLOW004_MANIFEST_MAGIC ||
            manifest.mcu_destination != SOC_MCI_TOP_MCU_SRAM_BASE_ADDR ||
            manifest.mcu_payload_bytes == 0u ||
            manifest.mcu_payload_bytes > sizeof(image) - FLOW004_HEADER_BYTES) {
            fail("invalid test manifest");
        }
    }
    if (stage == 2u &&
        (manifest.mcu_payload_bytes != image[2] ||
         manifest.mcu_checksum != image[3])) {
        fail("MCU image does not match the previously received manifest");
    }
    VPRINTF(LOW, "FLOW004: stage %u verified %u bytes in MCU SRAM\n",
            stage, words * 4u);
    publish(4u, 1u, (uint8_t)stage);
    cptra_usb_ocp_recovery_signal_state_generation(
        CPTRA_USB_OCP_FW_STATE_RECOVERY_PENDING, (uint8_t)stage,
        (uint16_t)(stage + 1u));
    if (cptra_usb_ocp_recovery_wait_image_activated(FLOW004_POLL_LIMIT)) {
        fail("fresh image activation timed out");
    }
    publish(5u, 2u, (uint8_t)stage);
    cptra_usb_ocp_recovery_signal_state_generation(
        CPTRA_USB_OCP_FW_STATE_FLOW_BOOTING_READY, (uint8_t)stage,
        (uint16_t)(stage + 1u));
    wait_command(CPTRA_USB_OCP_FW_COMMAND_FLOW_ADVANCE,
                 (uint16_t)(stage + 1u));
    if (cptra_usb_ocp_recovery_write_recovery_ctrl(
            cptra_usb_ocp_recovery_pack_ctrl(0u, 1u, 0xFFu))) {
        fail("activation clear failed");
    }
    next_stage++;
}

static void complete(void)
{
    if (next_stage != 3u) {
        fail("premature runtime completion");
    }
    VPRINTF(LOW, "FLOW004: downloaded Caliptra runtime authorizing MCU SRAM\n");
    cptra_usb_ocp_recovery_publish_completion();
    for (uint32_t poll = 0u; poll < FLOW004_POLL_LIMIT; ++poll) {
        if (lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) &
            MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) {
            if (lsu_read_32(CLP_MBOX_CSR_MBOX_CMD) != FLOW004_MCU_PASS ||
                lsu_read_32(CLP_MBOX_CSR_MBOX_DLEN) != 0u) {
                fail("unexpected MCU pass mailbox");
            }
            lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, CMD_COMPLETE);
            publish(5u, 3u, 2u);
            // Preserve GO after authorization; clearing it can request an update.
            lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0,
                4u | ((uint32_t)CPTRA_USB_OCP_FW_STATE_FLOW_SUCCESS_READY << 3)
                   | (2u << 11) | (3u << 19));
            wait_command(CPTRA_USB_OCP_FW_COMMAND_FLOW_COMPLETE, 4u);
            lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0,
                4u | ((uint32_t)CPTRA_USB_OCP_FW_STATE_FLOW_COMPLETE << 3)
                   | (2u << 11) | (4u << 19));
            VPRINTF(LOW, "FLOW004: all stages executed; MCU pass mailbox verified\n");
            while (1) {}
        }
        delay();
    }
    fail("downloaded MCU image did not send its pass mailbox");
}

void main(void)
{
    const flow004_services_t services = {
        FLOW004_MAGIC, receive_stage, complete
    };
    void (*entry)(const flow004_services_t *) =
        (void (*)(const flow004_services_t *))RV_ICCM_SADR;
    volatile uint32_t *iccm = (volatile uint32_t *)RV_ICCM_SADR;
    uint32_t poll;

    soc_ifc_set_flow_status_field(
        SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);
    for (poll = 0u; poll < FLOW004_POLL_LIMIT; ++poll) {
        if (lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) &
            MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) {
            break;
        }
        delay();
    }
    if (poll == FLOW004_POLL_LIMIT) {
        fail("initial MCU mailbox timed out");
    }
    lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, CMD_COMPLETE);
    receive_stage(0u);
    for (uint32_t i = 0u; i < image[2] / 4u; ++i) {
        iccm[i] = image[FLOW004_HEADER_BYTES / 4u + i];
        if (iccm[i] != image[FLOW004_HEADER_BYTES / 4u + i]) {
            fail("downloaded ICCM image readback mismatch");
        }
    }
    __asm__ volatile ("fence.i" ::: "memory");
    VPRINTF(LOW, "FLOW004: entering USB-downloaded Caliptra ICCM image\n");
    entry(&services);
    fail("downloaded Caliptra runtime returned unexpectedly");
}
