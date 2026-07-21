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
//
// Caliptra-core firmware for the USB OCP Recovery bring-up path.
// This test discovers the recovery aperture through the strap-published
// SS_RECOVERY_IFC_BASE_ADDR_L/H registers, drains the USB OCP recovery FIFO
// through the AXI DMA, writes RECOVERY_CTRL, and then asserts
// SS_GENERIC_FW_EXEC_CTRL_0[2] so the MCU can exit its USB event loop.

#include <stdint.h>

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"
#include "soc_ifc.h"
#include "usb_ocp_recovery_cptra.h"

#define CPTRA_OCP_RECOVERY_DEVICE_STATUS_READY_FOR_RECOVERY_IMAGE 0x03u
#define CPTRA_OCP_RECOVERY_DEVICE_STATUS_RECOVERY_PENDING 0x04u
#define OCP_RECOVERY_SCRATCH_WORDS 16u
#define OCP_RECOVERY_CMS_REGION 0u
#define OCP_RECOVERY_MBOX_DEST_ADDR 0x4400u
#define OCP_RECOVERY_POLL_DELAY_CYCLES 64u
#define OCP_RECOVERY_POLL_ITERS 50000u
#define OCP_RECOVERY_DMA_ERR_LIMIT 20u
#define SS_GENERIC_FW_EXEC_CTRL_GO_MASK (1u << 2)

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

static inline void spin_delay(uint32_t cycles) {
    for (uint32_t ii = 0; ii < cycles; ++ii) {
        __asm__ volatile ("nop");
    }
}

static void fail_and_halt(const char *msg) {
    VPRINTF(FATAL, "%s\n", msg);
    SEND_STDOUT_CTRL(0x1);
    while (1) {
    }
}

// Verify the drained recovery image matches the deterministic pattern the USB
// OCP-recovery DV sequence programs (caliptra_ss_usb_ocp_recovery_sequence.svh,
// step 5b): words 0..3 are fixed markers, words 4+ are 0x00000010 + word_index.
// This self-checks the ENTIRE recovery datapath (USB push -> FIFO -> AXI drain)
// for every DWORD, not just the first word.
static uint8_t cptra_ocp_recovery_check_image(const uint32_t *img, uint32_t words) {
    static const uint32_t markers[4] = {
        0xDEADBEEFu, 0xCAFEBABEu, 0x12345678u, 0x9ABCDEF0u };
    for (uint32_t i = 0u; i < words; ++i) {
        uint32_t expected = (i < 4u) ? markers[i] : (0x00000010u + i);
        if (img[i] != expected) {
            VPRINTF(FATAL,
                    "CPTRA: drained image mismatch at word %u: got 0x%08x exp 0x%08x\n",
                    i, img[i], expected);
            return 1u;
        }
    }
    return 0u;
}

void main(void) {
    uint32_t scratch[OCP_RECOVERY_SCRATCH_WORDS] = {0};
    uint32_t image_size_words;
    uint32_t last_write_index = 0u;
    uint32_t recovery_ctrl_word;
    uint64_t rec_base;
    uint8_t dev_status = 0u;
    uint8_t fifo_status;
    uint8_t poll_result;

    VPRINTF(LOW, "=======================================\n");
    VPRINTF(LOW, "Caliptra USB OCP recovery consumer test\n");
    VPRINTF(LOW, "=======================================\n");

    rec_base = cptra_usb_ocp_recovery_get_base();
    VPRINTF(LOW, "CPTRA: recovery aperture base lo=0x%08x hi=0x%08x\n",
            (uint32_t)rec_base,
            (uint32_t)(rec_base >> 32));
    if (rec_base != (uint64_t)SOC_USB_OCP_RECOVERY_REG_BASE_ADDR) {
        VPRINTF(WARNING,
                "CPTRA: SS_RECOVERY_IFC_BASE_ADDR!=SOC_USB_OCP_RECOVERY_REG_BASE_ADDR; using generated base 0x%08x\n",
                (uint32_t)SOC_USB_OCP_RECOVERY_REG_BASE_ADDR);
    }

    // Signal MCU that we are ready for mailbox commands. This allows MCU to
    // complete USB enumeration before sending RI_DOWNLOAD_FIRMWARE.
    VPRINTF(LOW, "CPTRA: setting READY_FOR_MB_PROCESSING\n");
    soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    // Wait for RI_DOWNLOAD_FIRMWARE mailbox command from MCU. This ensures
    // USB enumeration is complete before we start DMA polling, avoiding AXI
    // bus contention that would cause USB timing violations (tend_to_end_delay).
    VPRINTF(LOW, "CPTRA: waiting for RI_DOWNLOAD_FIRMWARE mailbox command\n");
    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE)
            & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 0u) {
        spin_delay(OCP_RECOVERY_POLL_DELAY_CYCLES);
    }
    VPRINTF(LOW, "CPTRA: RI_DOWNLOAD_FIRMWARE received; starting OCP recovery flow\n");

    // Immediately acknowledge the mailbox command so MCU can enter the USB
    // event loop. The mailbox command is a "start" signal; MCU must continue
    // servicing USB while Caliptra runs the OCP recovery flow.
    VPRINTF(LOW, "CPTRA: acknowledging RI_DOWNLOAD_FIRMWARE (MBOX_STATUS=CMD_COMPLETE)\n");
    lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, (uint32_t)CMD_COMPLETE);

    VPRINTF(LOW, "CPTRA: polling DEVICE_STATUS for Recovery Pending (iters=%u, dma_err_limit=%u)\n",
            OCP_RECOVERY_POLL_ITERS, OCP_RECOVERY_DMA_ERR_LIMIT);

    poll_result = cptra_usb_ocp_recovery_poll_device_status(
        CPTRA_OCP_RECOVERY_DEVICE_STATUS_RECOVERY_PENDING,
        OCP_RECOVERY_POLL_ITERS,
        OCP_RECOVERY_DMA_ERR_LIMIT,
        &dev_status);

    if (poll_result == 1u) {
        VPRINTF(FATAL, "CPTRA: DEVICE_STATUS DMA read failed after retries (last_status=0x%02x)\n", dev_status);
        fail_and_halt("CPTRA: unrecoverable DMA error in DEVICE_STATUS poll");
    } else if (poll_result == 2u) {
        VPRINTF(WARNING, "CPTRA: DEVICE_STATUS poll timed out (last_status=0x%02x)\n", dev_status);
        if (dev_status < CPTRA_OCP_RECOVERY_DEVICE_STATUS_READY_FOR_RECOVERY_IMAGE) {
            fail_and_halt("CPTRA: recovery never reached READY_FOR_RECOVERY_IMAGE state");
        }
        // Continue with fallback drain if we at least reached READY_FOR_RECOVERY_IMAGE
        VPRINTF(LOW, "CPTRA: proceeding with fallback drain (status=0x%02x)\n", dev_status);
    } else {
        VPRINTF(LOW, "CPTRA: DEVICE_STATUS reached Recovery Pending (0x04)\n");
    }

    image_size_words = cptra_usb_ocp_recovery_read_image_size_words();
    if (image_size_words == 0u) {
        // OCP Recovery v1.1 Sec 9.2: by the time DEVICE_STATUS reports the
        // recovery image is available, the device must have programmed a
        // non-zero IMAGE_SIZE via INDIRECT_FIFO_CTRL. A zero here is a genuine
        // protocol/programming error, not a condition to silently work around.
        fail_and_halt("CPTRA: INDIRECT_FIFO_CTRL IMAGE_SIZE read back as zero");
    }
    if (image_size_words > OCP_RECOVERY_SCRATCH_WORDS) {
        fail_and_halt("CPTRA: IMAGE_SIZE exceeds drain scratch capacity");
    }
    if (cptra_usb_ocp_recovery_read_fifo_status(
            &fifo_status, &last_write_index) != 0u) {
        fail_and_halt("CPTRA: INDIRECT_FIFO_STATUS DMA read failed");
    }
    VPRINTF(LOW, "CPTRA: fifo_status=0x%02x write_index=0x%08x before drain\n",
            fifo_status,
            last_write_index);
    VPRINTF(LOW, "CPTRA: draining %u dwords from INDIRECT_FIFO_DATA\n", image_size_words);
    if (cptra_usb_ocp_recovery_drain_fifo(
            image_size_words,
            scratch,
            OCP_RECOVERY_SCRATCH_WORDS) != 0u) {
        fail_and_halt("CPTRA: INDIRECT_FIFO_DATA DMA drain failed");
    }
    if (cptra_usb_ocp_recovery_read_fifo_status(
            &fifo_status, &last_write_index) != 0u) {
        fail_and_halt("CPTRA: post-drain INDIRECT_FIFO_STATUS DMA read failed");
    }
    VPRINTF(LOW, "CPTRA: drained %u dwords; final write_index=0x%08x fifo_status=0x%02x first_word=0x%08x\n",
            image_size_words,
            last_write_index,
            fifo_status,
            scratch[0]);

    if (cptra_ocp_recovery_check_image(scratch, image_size_words) != 0u) {
        fail_and_halt("CPTRA: drained recovery image content mismatch");
    }
    VPRINTF(LOW, "CPTRA: drained image content verified (%u dwords)\n", image_size_words);

    VPRINTF(LOW, "CPTRA: clearing RECOVERY_CTRL activation after verified FIFO drain\n");
    if (cptra_usb_ocp_recovery_read_dword_retry(
            SOC_USB_OCP_RECOVERY_REG_RECOVERY_CTRL,
            &recovery_ctrl_word) != 0u) {
        fail_and_halt("CPTRA: RECOVERY_CTRL read before activation clear failed");
    }
    recovery_ctrl_word &= 0xFF00FFFFu;
    if (cptra_usb_ocp_recovery_write_dword(
            SOC_USB_OCP_RECOVERY_REG_RECOVERY_CTRL,
            recovery_ctrl_word) != 0u) {
        fail_and_halt("CPTRA: RECOVERY_CTRL activation clear write failed");
    }

    VPRINTF(LOW, "CPTRA: signaling MCU completion through SS_GENERIC_FW_EXEC_CTRL_0[2]\n");
    // Match the established convention in existing tests (mcu_lmem_exe,
    // smoke_test_mcu_hitless, caliptra_ss_usb_init/cptra_bringup): direct
    // write of the GO mask, no RMW. The register has no RW1C/sticky fields,
    // and a RMW races with MCU reads of the same register.
    lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0, SS_GENERIC_FW_EXEC_CTRL_GO_MASK);

    while (1);
}
