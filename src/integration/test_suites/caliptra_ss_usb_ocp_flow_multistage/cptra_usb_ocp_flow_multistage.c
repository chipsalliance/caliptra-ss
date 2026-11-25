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

static void verify_sha384(const uint8_t *payload, uint32_t bytes,
                          const uint32_t *expected)
{
    uint32_t poll;

    for (poll = 0u; poll < FLOW004_POLL_LIMIT; ++poll) {
        if ((lsu_read_32(CLP_SHA512_ACC_CSR_LOCK) &
             SHA512_ACC_CSR_LOCK_LOCK_MASK) == 0u) {
            break;
        }
        delay();
    }
    if (poll == FLOW004_POLL_LIMIT) {
        fail("SHA-384 accelerator lock acquisition timed out");
    }
    VPRINTF(LOW, "FLOW004: SHA-384 lock acquired, streaming %u bytes\n", bytes);
    soc_ifc_sha_accel_wr_mode(SHA_STREAM_384);
    lsu_write_32(CLP_SHA512_ACC_CSR_DLEN, bytes);
    // The shared driver selects ENDIAN_TOGGLE; DATAIN takes big-endian words.
    for (uint32_t i = 0u; i < bytes; i += 4u) {
        uint32_t word = ((uint32_t)payload[i] << 24) |
                        ((uint32_t)payload[i + 1u] << 16) |
                        ((uint32_t)payload[i + 2u] << 8) |
                        (uint32_t)payload[i + 3u];
        lsu_write_32(CLP_SHA512_ACC_CSR_DATAIN, word);
    }
    soc_ifc_sha_accel_execute();
    VPRINTF(LOW, "FLOW004: SHA-384 execution requested\n");
    for (poll = 0u; poll < FLOW004_POLL_LIMIT; ++poll) {
        if (lsu_read_32(CLP_SHA512_ACC_CSR_STATUS) &
            SHA512_ACC_CSR_STATUS_VALID_MASK) {
            break;
        }
        delay();
    }
    if (poll == FLOW004_POLL_LIMIT) {
        soc_ifc_sha_accel_clr_lock();
        fail("SHA-384 accelerator timed out");
    }
    for (uint32_t i = 0u; i < FLOW004_DIGEST_WORDS; ++i) {
        uint32_t actual = lsu_read_32(CLP_SHA512_ACC_CSR_DIGEST_0 + 4u * i);
        if (actual != expected[i]) {
            VPRINTF(FATAL, "FLOW004: SHA-384 digest[%u] got=%08x expected=%08x\n",
                    i, actual, expected[i]);
            soc_ifc_sha_accel_clr_lock();
            fail("complete image SHA-384 digest mismatch");
        }
    }
    soc_ifc_sha_accel_clr_lock();
}

static void receive_stage(uint32_t stage)
{
    uint32_t words, pages;
    uint32_t payload_word = FLOW004_HEADER_BYTES / 4u;
    uint8_t *payload = (uint8_t *)image + FLOW004_HEADER_BYTES;

    if (stage != next_stage || stage > 2u) {
        fail("downloaded runtime requested stages out of order");
    }
    VPRINTF(LOW, "FLOW004: stage %u receiver entered\n", stage);
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
    VPRINTF(LOW, "FLOW004: stage %u draining %u bytes to SRAM\n", stage, words * 4u);
    if (cptra_usb_ocp_recovery_stream_fifo_to_axi(
            SOC_MCI_TOP_MCU_SRAM_BASE_ADDR, words * 4u, 64u)) {
        fail("image FIFO-to-SRAM DMA failed");
    }
    VPRINTF(LOW, "FLOW004: stage %u DMA complete, reading SRAM\n", stage);
    if (cptra_usb_ocp_recovery_read_axi_payload(
            SOC_MCI_TOP_MCU_SRAM_BASE_ADDR, image, words * 4u)) {
        fail("image SRAM verification read failed");
    }
    VPRINTF(LOW, "FLOW004: stage %u SRAM read complete, verifying SHA-384\n", stage);
    if (image[0] != FLOW004_MAGIC || image[1] != stage ||
        image[2] != words * 4u - FLOW004_HEADER_BYTES ||
        image[3] != FLOW004_FORMAT_VERSION) {
        fail("image header/identity check failed");
    }
    verify_sha384(payload, image[2], &image[4]);
    if (stage == 1u) {
        if (image[2] < sizeof(manifest)) {
            fail("truncated test manifest");
        }
        manifest.magic = image[payload_word];
        manifest.mcu_destination = image[payload_word + 1u];
        manifest.mcu_payload_bytes = image[payload_word + 2u];
        for (uint32_t i = 0u; i < FLOW004_DIGEST_WORDS; ++i) {
            manifest.mcu_digest[i] = image[payload_word + 3u + i];
        }
        if (manifest.magic != FLOW004_MANIFEST_MAGIC ||
            manifest.mcu_destination != SOC_MCI_TOP_MCU_SRAM_BASE_ADDR ||
            manifest.mcu_payload_bytes == 0u ||
            manifest.mcu_payload_bytes > sizeof(image) - FLOW004_HEADER_BYTES) {
            fail("invalid test manifest");
        }
    }
    if (stage == 2u) {
        if (manifest.mcu_payload_bytes != image[2]) {
            fail("MCU image size does not match the previously received manifest");
        }
        for (uint32_t i = 0u; i < FLOW004_DIGEST_WORDS; ++i) {
            if (manifest.mcu_digest[i] != image[4u + i]) {
                fail("MCU digest does not match the previously received manifest");
            }
        }
    }
    VPRINTF(LOW, "FLOW004: stage %u SHA-384 verified %u bytes in MCU SRAM\n",
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

    soc_ifc_sha_accel_clr_lock();
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
    // Finalize the ICCM write-snoop measurement so hardware releases SHA.
    soc_ifc_set_iccm_lock();
    __asm__ volatile ("fence.i" ::: "memory");
    VPRINTF(LOW, "FLOW004: entering USB-downloaded Caliptra ICCM image\n");
    entry(&services);
    fail("downloaded Caliptra runtime returned unexpectedly");
}
