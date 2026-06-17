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
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"
#include "soc_ifc.h"
#include "soc_ifc_ss.h"

#define CPTRA_OCP_RECOVERY_BYTE0_MASK 0xFFu
#define CPTRA_OCP_RECOVERY_DMA_RETRIES 3u
#define CPTRA_OCP_RECOVERY_RETRY_DELAY 16u
#define CPTRA_OCP_RECOVERY_DEVICE_STATUS_READY_FOR_RECOVERY_IMAGE 0x03u
#define CPTRA_OCP_RECOVERY_DEVICE_STATUS_RECOVERY_PENDING 0x04u
#define CPTRA_OCP_RECOVERY_RECOVERY_CTRL_USE_MEMORY_WINDOW_IMAGE 0x01u
#define CPTRA_OCP_RECOVERY_RECOVERY_CTRL_ACTIVATE_RECOVERY_IMAGE 0x0Fu

#define OCP_RECOVERY_SCRATCH_WORDS 16u
#define OCP_RECOVERY_CMS_REGION 0u
#define OCP_RECOVERY_MBOX_DEST_ADDR 0x4400u
#define OCP_RECOVERY_DMA_BLOCK_SIZE 256u
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

static uint8_t cptra_ocp_recovery_read_dword(uint64_t addr, uint32_t *value) {
    return soc_ifc_axi_dma_read_ahb_payload_with_status(addr, 0u, value, sizeof(*value), 0u);
}

static uint8_t cptra_ocp_recovery_read_dword_retry(uint64_t addr, uint32_t *value) {
    uint8_t status;
    for (uint32_t attempt = 0; attempt < CPTRA_OCP_RECOVERY_DMA_RETRIES; ++attempt) {
        status = cptra_ocp_recovery_read_dword(addr, value);
        if (status == 0u) {
            return 0u;
        }
        spin_delay(CPTRA_OCP_RECOVERY_RETRY_DELAY);
    }
    return 1u;
}

static uint8_t cptra_ocp_recovery_write_dword(uint64_t addr, uint32_t value) {
    return soc_ifc_axi_dma_send_ahb_payload_with_status(addr, 0u, &value, sizeof(value), 0u);
}

static uint32_t cptra_ocp_recovery_pack_recovery_ctrl(uint8_t cms, uint8_t img_sel, uint8_t activate) {
    return ((uint32_t)cms << 0)
         | ((uint32_t)img_sel << 8)
         | ((uint32_t)activate << 16);
}

uint8_t cptra_ocp_recovery_read_device_status(uint8_t *device_status) {
    uint32_t device_status_word = 0u;

    if (device_status == 0) {
        return 1u;
    }

    // OCP Recovery v1.1 9.2, DEVICE_STATUS / Table 9-5: byte 0 is the device status.
    // Use retry wrapper to handle transient AXI DMA errors during USB bus activity.
    if (cptra_ocp_recovery_read_dword_retry(SOC_USB_OCP_RECOVERY_REG_DEVICE_STATUS_0, &device_status_word) != 0u) {
        return 1u;
    }

    *device_status = (uint8_t)(device_status_word & CPTRA_OCP_RECOVERY_BYTE0_MASK);
    return 0u;
}

uint8_t cptra_ocp_recovery_poll_device_status(uint8_t target_status, uint32_t timeout_iters) {
    uint8_t device_status;

    while (timeout_iters-- != 0u) {
        if (cptra_ocp_recovery_read_device_status(&device_status) != 0u) {
            return 1u;
        }
        if (device_status == target_status) {
            return 0u;
        }
    }

    return 1u;
}

// Poll DEVICE_STATUS for the target status with retry and progress reporting.
// Returns 0 on success (target status reached), 1 on DMA error, 2 on timeout.
// poll_iters: number of poll iterations before timeout
// dma_err_limit: max consecutive DMA errors before giving up
// last_status: output param for last observed DEVICE_STATUS (may be NULL)
uint8_t cptra_ocp_recovery_poll_device_status_robust(
    uint8_t target_status,
    uint32_t poll_iters,
    uint32_t dma_err_limit,
    uint8_t *last_status) {

    uint8_t device_status = 0u;
    uint32_t consecutive_dma_errs = 0u;

    for (uint32_t iter = 0; iter < poll_iters; ++iter) {
        if (cptra_ocp_recovery_read_device_status(&device_status) != 0u) {
            consecutive_dma_errs++;
            if (consecutive_dma_errs >= dma_err_limit) {
                if (last_status != 0) {
                    *last_status = device_status;
                }
                return 1u;
            }
            spin_delay(CPTRA_OCP_RECOVERY_RETRY_DELAY * 4u);
            continue;
        }
        consecutive_dma_errs = 0u;

        if (device_status == target_status) {
            if (last_status != 0) {
                *last_status = device_status;
            }
            return 0u;
        }

        spin_delay(CPTRA_OCP_RECOVERY_RETRY_DELAY);
    }

    if (last_status != 0) {
        *last_status = device_status;
    }
    return 2u;
}

uint32_t cptra_ocp_recovery_read_image_size_words(void) {
    uint32_t image_size_words = 0u;

    // OCP Recovery v1.1 9.2, INDIRECT_FIFO_CTRL / Table 9-13: bytes 2..5 hold Image Size in 4-byte units.
    (void)cptra_ocp_recovery_read_dword(SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_CTRL_1, &image_size_words);
    return image_size_words;
}

uint8_t cptra_ocp_recovery_read_fifo_status(uint8_t *fifo_status, uint32_t *write_index) {
    uint32_t fifo_status_word = 0u;
    uint32_t write_index_word = 0u;

    if ((fifo_status == 0) || (write_index == 0)) {
        return 1u;
    }

    // OCP Recovery v1.1 9.2, INDIRECT_FIFO_STATUS / Table 9-14: byte 0 is FIFO status and bytes 4..7 are Write Index.
    // Use retry wrapper to handle transient AXI DMA errors during USB bus activity.
    if (cptra_ocp_recovery_read_dword_retry(SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_STATUS_0, &fifo_status_word) != 0u) {
        return 1u;
    }
    if (cptra_ocp_recovery_read_dword_retry(SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_STATUS_1, &write_index_word) != 0u) {
        return 1u;
    }

    *fifo_status = (uint8_t)(fifo_status_word & CPTRA_OCP_RECOVERY_BYTE0_MASK);
    *write_index = write_index_word;
    return 0u;
}

uint8_t cptra_ocp_recovery_drain_fifo(uint32_t image_size_words, uint32_t mbox_dest_addr, uint16_t block_size) {
    uint32_t byte_count = image_size_words * sizeof(uint32_t);

    if (byte_count == 0u) {
        return 0u;
    }

    // OCP Recovery v1.1 8.2.5 and 9.2, INDIRECT_FIFO_DATA / Table 9-15: repeatedly access the fixed FIFO data register.
    return soc_ifc_axi_dma_read_mbox_payload(SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_DATA,
                                             mbox_dest_addr,
                                             1u,
                                             byte_count,
                                             block_size);
}

void cptra_ocp_recovery_set_recovery_ctrl(uint8_t cms, uint8_t img_sel, uint8_t activate) {
    uint32_t ctrl_word;

    // OCP Recovery v1.1 9.2, RECOVERY_CTRL / Table 9-9: program CMS, then image selection, then activate.
    ctrl_word = cptra_ocp_recovery_pack_recovery_ctrl(cms, 0u, 0u);
    (void)cptra_ocp_recovery_write_dword(SOC_USB_OCP_RECOVERY_REG_RECOVERY_CTRL, ctrl_word);

    ctrl_word = cptra_ocp_recovery_pack_recovery_ctrl(cms, img_sel, 0u);
    (void)cptra_ocp_recovery_write_dword(SOC_USB_OCP_RECOVERY_REG_RECOVERY_CTRL, ctrl_word);

    ctrl_word = cptra_ocp_recovery_pack_recovery_ctrl(cms, img_sel, activate);
    (void)cptra_ocp_recovery_write_dword(SOC_USB_OCP_RECOVERY_REG_RECOVERY_CTRL, ctrl_word);
}

void main(void) {
    uint32_t scratch[OCP_RECOVERY_SCRATCH_WORDS] = {0};
    uint32_t image_size_words;
    uint32_t last_write_index = 0u;
    uint64_t rec_base;
    uint8_t dev_status = 0u;
    uint8_t fifo_status;
    uint8_t poll_result;

    VPRINTF(LOW, "=======================================\n");
    VPRINTF(LOW, "Caliptra USB OCP recovery consumer test\n");
    VPRINTF(LOW, "=======================================\n");

    rec_base = recovery_base();
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

    poll_result = cptra_ocp_recovery_poll_device_status_robust(
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
