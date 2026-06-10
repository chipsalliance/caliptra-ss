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
// Per plan D0.E, this test discovers the recovery aperture through the
// strap-published SS_RECOVERY_IFC_BASE_ADDR_L/H registers, drains the USB OCP
// recovery FIFO through the AXI DMA, writes RECOVERY_CTRL, and then asserts
// SS_GENERIC_FW_EXEC_CTRL_0[2] so the MCU can exit its USB event loop.

#include <stdint.h>

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "cptra_usb_ocp_recovery.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"

#define OCP_RECOVERY_SCRATCH_WORDS 16u
#define OCP_RECOVERY_CMS_REGION 0u
#define OCP_RECOVERY_MBOX_DEST_ADDR 0x4400u
#define OCP_RECOVERY_DMA_BLOCK_SIZE 256u
#define OCP_RECOVERY_POLL_DELAY_CYCLES 64u
#define SS_GENERIC_FW_EXEC_CTRL_GO_MASK (1u << 2)

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

static inline uint64_t recovery_base(void) {
    uint64_t lo = (uint64_t)lsu_read_32(CLP_SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_L);
    uint64_t hi = (uint64_t)lsu_read_32(CLP_SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_H);
    return (hi << 32) | lo;
}

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

void main(void) {
    uint32_t scratch[OCP_RECOVERY_SCRATCH_WORDS] = {0};
    uint32_t image_size_words;
    uint32_t last_write_index = 0u;
    uint64_t rec_base;
    uint8_t dev_status;
    uint8_t fifo_status;
    uint8_t saw_ready_for_recovery_image;

    VPRINTF(LOW, "=======================================\n");
    VPRINTF(LOW, "Caliptra USB OCP recovery consumer test\n");
    VPRINTF(LOW, "=======================================\n");

    rec_base = recovery_base();
    VPRINTF(LOW, "CPTRA: recovery aperture base lo=0x%08x hi=0x%08x\n",
            (uint32_t)rec_base,
            (uint32_t)(rec_base >> 32));
    if (rec_base != (uint64_t)SOC_USB_OCP_RECOVERY_BASE_ADDR) {
        VPRINTF(WARNING,
                "CPTRA: SS_RECOVERY_IFC_BASE_ADDR!=SOC_USB_OCP_RECOVERY_BASE_ADDR; using generated base 0x%08x\n",
                (uint32_t)SOC_USB_OCP_RECOVERY_BASE_ADDR);
    }

    VPRINTF(LOW, "CPTRA: polling DEVICE_STATUS for Recovery Pending\n");
    saw_ready_for_recovery_image = 0u;
    while (1) {
        if (cptra_ocp_recovery_read_device_status(&dev_status) != 0u) {
            fail_and_halt("CPTRA: DEVICE_STATUS DMA read failed");
        }
        if (dev_status == CPTRA_OCP_RECOVERY_DEVICE_STATUS_RECOVERY_PENDING) {
            break;
        }
        if (dev_status == CPTRA_OCP_RECOVERY_DEVICE_STATUS_READY_FOR_RECOVERY_IMAGE) {
            saw_ready_for_recovery_image = 1u;
        }
        spin_delay(OCP_RECOVERY_POLL_DELAY_CYCLES);
    }
    if (saw_ready_for_recovery_image != 0u) {
        VPRINTF(LOW, "CPTRA: observed DEVICE_STATUS=0x03 before Recovery Pending\n");
    }

    image_size_words = cptra_ocp_recovery_read_image_size_words();
    if (image_size_words == 0u) {
        image_size_words = OCP_RECOVERY_SCRATCH_WORDS;
        VPRINTF(WARNING, "CPTRA: image size is zero; falling back to a 64-byte bring-up drain\n");
    }
    if (cptra_ocp_recovery_read_fifo_status(&fifo_status, &last_write_index) != 0u) {
        fail_and_halt("CPTRA: INDIRECT_FIFO_STATUS DMA read failed");
    }
    VPRINTF(LOW, "CPTRA: fifo_status=0x%02x write_index=0x%08x before drain\n",
            fifo_status,
            last_write_index);
    VPRINTF(LOW, "CPTRA: draining %u dwords from INDIRECT_FIFO_DATA\n", image_size_words);
    if (cptra_ocp_recovery_drain_fifo(image_size_words,
                                      OCP_RECOVERY_MBOX_DEST_ADDR,
                                      OCP_RECOVERY_DMA_BLOCK_SIZE) != 0u) {
        fail_and_halt("CPTRA: INDIRECT_FIFO_DATA DMA drain failed");
    }
    if (cptra_ocp_recovery_read_fifo_status(&fifo_status, &last_write_index) != 0u) {
        fail_and_halt("CPTRA: post-drain INDIRECT_FIFO_STATUS DMA read failed");
    }
    for (uint32_t ii = 0; (ii < image_size_words) && (ii < OCP_RECOVERY_SCRATCH_WORDS); ++ii) {
        scratch[ii] = lsu_read_32(CLP_MBOX_SRAM_BASE_ADDR + OCP_RECOVERY_MBOX_DEST_ADDR + (ii << 2));
    }
    VPRINTF(LOW, "CPTRA: drained %u dwords; final write_index=0x%08x fifo_status=0x%02x first_word=0x%08x\n",
            image_size_words,
            last_write_index,
            fifo_status,
            scratch[0]);

    VPRINTF(LOW, "CPTRA: writing RECOVERY_CTRL to select CMS image and activate it\n");
    cptra_ocp_recovery_set_recovery_ctrl(OCP_RECOVERY_CMS_REGION,
                                         CPTRA_OCP_RECOVERY_RECOVERY_CTRL_USE_MEMORY_WINDOW_IMAGE,
                                         CPTRA_OCP_RECOVERY_RECOVERY_CTRL_ACTIVATE_RECOVERY_IMAGE);

    VPRINTF(LOW, "CPTRA: signaling MCU completion through SS_GENERIC_FW_EXEC_CTRL_0[2]\n");
    // Match the established convention in existing tests (mcu_lmem_exe,
    // smoke_test_mcu_hitless, caliptra_ss_usb_init/cptra_bringup): direct
    // write of the GO mask, no RMW. The register has no RW1C/sticky fields,
    // and a RMW races with MCU reads of the same register.
    lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0, SS_GENERIC_FW_EXEC_CTRL_GO_MASK);

    SEND_STDOUT_CTRL(0xff);
    while (1) {
    }
}
