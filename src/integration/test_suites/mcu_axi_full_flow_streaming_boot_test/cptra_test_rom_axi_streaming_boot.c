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
// Description: Caliptra FW (Device Firmware) for 3-image AXI bypass
//              recovery flow per axi_recovery_flow.md.
//
// Image stages:
//   Stage 0: 8 bytes   (2 DWORDs)  - REC_IMG_INDEX = 0
//   Stage 1: 512 bytes (128 DWORDs) - REC_IMG_INDEX = 1
//   Stage 2: 516 bytes (129 DWORDs) - REC_IMG_INDEX = 2
//
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
#include "soc_ifc.h"
#include "caliptra_reg.h"
#include "soc_address_map.h"

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define NUM_STAGES 3
#define DMA_BLOCK_SIZE 64

// MCU SRAM destination offsets for each stage (non-overlapping)
// Stage 0:   8B at offset 0x0000
// Stage 1: 512B at offset 0x1000
// Stage 2: 516B at offset 0x2000
static const uint32_t mcu_sram_offsets[NUM_STAGES] = { 0x0000, 0x1000, 0x2000 };

// ============================================================
// Helper functions
// ============================================================

// Step 1: Write PROT_CAP_2 with recovery capabilities
void update_prot_cap() {

    uint32_t i3c_reg_data;

    VPRINTF(LOW, "CPTRA: executing update_prot_cap\n");

    i3c_reg_data = 0x00000000;
    i3c_reg_data = 0x1 << (0  + 0)  | i3c_reg_data; // Major version
    i3c_reg_data = 0x1 << (8  + 0)  | i3c_reg_data; // Minor version
    i3c_reg_data = 0x1 << (16 + 7)  | i3c_reg_data; // Push-C-Image support
    i3c_reg_data = 0x1 << (16 + 11) | i3c_reg_data; // Flashless boot (from reset)
    i3c_reg_data = 0x1 << (16 + 12) | i3c_reg_data; // FIFO CMS support
    VPRINTF(LOW, "CPTRA: Writing PROT_CAP_2 with 0x%x\n", i3c_reg_data);
    soc_ifc_axi_dma_send_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_2, 0, &i3c_reg_data, 4, 0);
}

// Step 2: Write DEVICE_STATUS_0
void update_device_status(uint32_t device_status) {
    VPRINTF(LOW, "CPTRA: Writing DEVICE_STATUS_0 with 0x%x\n", device_status);
    soc_ifc_axi_dma_send_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0, 0, &device_status, 4, 0);
}

// Step 3: Write RECOVERY_STATUS (DEV_REC_STATUS + REC_IMG_INDEX)
void update_recovery_status(uint32_t recovery_status) {

    uint32_t dev_rec_status;
    dev_rec_status = recovery_status & I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS_DEV_REC_STATUS_MASK;

    switch (dev_rec_status) {
        case 0x0: VPRINTF(LOW, "CPTRA: Recovery Status: Not in recovery mode\n"); break;
        case 0x1: VPRINTF(LOW, "CPTRA: Recovery Status: Awaiting recovery image\n"); break;
        case 0x2: VPRINTF(LOW, "CPTRA: Recovery Status: Processing image\n"); break;
        case 0x3: VPRINTF(LOW, "CPTRA: Recovery Status: Recovery successful\n"); break;
        default:  VPRINTF(LOW, "CPTRA: Recovery Status: 0x%x\n", dev_rec_status); break;
    }

    VPRINTF(LOW, "CPTRA: Writing RECOVERY_STATUS with 0x%x\n", recovery_status);
    soc_ifc_axi_dma_send_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS, 0, &recovery_status, 4, 0);
}

// Poll DMA STATUS0 for payload_available
void poll_for_payload_available() {

    uint32_t reg_data;

    for (uint16_t slp = 0; slp < 500; slp++) {
        reg_data = lsu_read_32(CLP_AXI_DMA_REG_STATUS0) & AXI_DMA_REG_STATUS0_PAYLOAD_AVAILABLE_MASK;
        if (reg_data != 0) {
            VPRINTF(LOW, "CPTRA: Payload is available\n");
            return;
        }
        for (uint16_t ii = 0; ii < 1000; ii++) {
            __asm__ volatile ("nop");
        }
    }
    VPRINTF(ERROR, "CPTRA: Payload not available after 500 attempts\n");
    SEND_STDOUT_CTRL(0x1);
    while(1);
}

// Wait for payload_available to deassert.
// Used between stages to avoid reading stale IMAGE_SIZE from a prior stage.
// MCU clears REC_PAYLOAD_DONE which causes payload_available to drop.
void wait_for_payload_not_available() {

    uint32_t reg_data;

    VPRINTF(LOW, "CPTRA: Waiting for payload_available to deassert\n");
    for (uint16_t slp = 0; slp < 500; slp++) {
        reg_data = lsu_read_32(CLP_AXI_DMA_REG_STATUS0) & AXI_DMA_REG_STATUS0_PAYLOAD_AVAILABLE_MASK;
        if (reg_data == 0) {
            VPRINTF(LOW, "CPTRA: payload_available deasserted\n");
            return;
        }
        for (uint16_t ii = 0; ii < 1000; ii++) {
            __asm__ volatile ("nop");
        }
    }
    VPRINTF(ERROR, "CPTRA: payload_available still asserted after 500 attempts\n");
    SEND_STDOUT_CTRL(0x1);
    while(1);
}

// Read image size from INDIRECT_FIFO_CTRL_1
uint32_t read_image_size() {

    uint32_t i3c_reg_data;

    soc_ifc_axi_dma_read_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_1, 0, &i3c_reg_data, 4, 0);
    VPRINTF(LOW, "CPTRA: Image Size = 0x%x DWORDs (%d bytes)\n", i3c_reg_data, i3c_reg_data * 4);
    return i3c_reg_data;
}

// DMA read from recovery FIFO to MCU SRAM via AXI-to-AXI transfer
void read_image_from_fifo_to_mcu_sram(uint32_t fw_image_size, uint32_t sram_offset) {

    uint64_t src_addr = (uint64_t)SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_DATA;
    uint64_t dst_addr = (uint64_t)SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + sram_offset;

    VPRINTF(LOW, "CPTRA: AXI-to-AXI DMA: %d DWORDs from FIFO to MCU SRAM offset 0x%x\n",
            fw_image_size, sram_offset);
    soc_ifc_axi_dma_send_axi_to_axi(
        src_addr,           // src: INDIRECT_FIFO_DATA
        1,                  // src_fixed: true (FIFO read address)
        dst_addr,           // dst: MCU SRAM
        0,                  // dst_fixed: false (incrementing)
        fw_image_size * 4,  // byte_count
        DMA_BLOCK_SIZE,     // block_size (64 = 256 bytes per payload_available pulse)
        0,                  // aes_mode: disabled
        0                   // aes_gcm_mode: disabled
    );
    VPRINTF(LOW, "CPTRA: DMA transfer complete\n");
}

// Step 12: Poll RECOVERY_CTRL.ACTIVATE_REC_IMG until == 0xF
void read_image_activation() {

    uint32_t i3c_reg_data;

    for (uint16_t slp = 0; slp < 100; slp++) {

        soc_ifc_axi_dma_read_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL, 0, &i3c_reg_data, 4, 0);
        i3c_reg_data = (i3c_reg_data & I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL_ACTIVATE_REC_IMG_MASK)
                       >> I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL_ACTIVATE_REC_IMG_LOW;
        if (i3c_reg_data == 0x0F) {
            VPRINTF(LOW, "CPTRA: ACTIVATE_REC_IMG == 0xF\n");
            return;
        }

        // Also check DMA STATUS0 IMAGE_ACTIVATED
        i3c_reg_data = lsu_read_32(CLP_AXI_DMA_REG_STATUS0) & AXI_DMA_REG_STATUS0_IMAGE_ACTIVATED_MASK;
        if (i3c_reg_data != 0) {
            VPRINTF(LOW, "CPTRA: Image Activation detected via DMA STATUS0\n");
            return;
        }

        for (uint8_t ii = 0; ii < 16; ii++) {
            __asm__ volatile ("nop");
        }
    }
    VPRINTF(ERROR, "CPTRA: Image Activation timeout\n");
}

// Clear ACTIVATE_REC_IMG via RECOVERY_CTRL
void update_recovery_ctrl(uint32_t recovery_ctrl) {

    VPRINTF(LOW, "CPTRA: Writing RECOVERY_CTRL with 0x%x\n", recovery_ctrl);
    soc_ifc_axi_dma_send_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL, 0, &recovery_ctrl, 4, 0);
}

// Reset the indirect FIFO via INDIRECT_FIFO_CTRL_0.RESET
void reset_indirect_fifo() {

    uint32_t i3c_reg_data;
    i3c_reg_data = I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_0_RESET_MASK;
    VPRINTF(LOW, "CPTRA: Resetting Indirect FIFO\n");
    soc_ifc_axi_dma_send_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_0, 0, &i3c_reg_data, 4, 0);
}

// Simple wait
void wait(uint32_t wait_time) {
    for (uint32_t ii = 0; ii < wait_time; ii++) {
        for (uint8_t jj = 0; jj < 16; jj++) {
            __asm__ volatile ("nop");
        }
    }
}

// ============================================================
// Multi-stage recovery sequence per axi_recovery_flow.md
// Matches caliptra-sw DmaRecovery::request_image() flow.
// ============================================================
void recovery_sequence() {

    uint32_t fw_image_size;
    uint32_t i3c_reg_data;
    uint32_t recovery_status_val;

    for (uint32_t stage = 0; stage < NUM_STAGES; stage++) {

        VPRINTF(LOW, "CPTRA: ========== Stage %d ==========\n", stage);

        // request_image() writes PROT_CAP_2 every stage
        update_prot_cap();

        // Step 2: DEVICE_STATUS_0.DEV_STATUS = 0x3 with FSB reason code
        i3c_reg_data = 0x3 | (0x12 << 16);
        update_device_status(i3c_reg_data);

        // Step 3: RECOVERY_STATUS with DEV_REC_STATUS = 0x1, REC_IMG_INDEX = stage
        recovery_status_val = 0x1 | (stage << I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS_REC_IMG_INDEX_LOW);
        update_recovery_status(recovery_status_val);

        // Step 3a: Wait for payload_available to deassert.
        // No-op on first stage (REC_PAYLOAD_DONE was never set).
        // On subsequent stages, waits for Image Provider to clear
        // REC_PAYLOAD_DONE at step 17.
        wait_for_payload_not_available();

        // Wait for payload from Image Provider (DMA payload_available)
        poll_for_payload_available();

        // Read image size
        fw_image_size = read_image_size();

        // DMA read image from FIFO into mailbox
        read_image_from_fifo_to_mcu_sram(fw_image_size, mcu_sram_offsets[stage]);

        // Step 11: DEVICE_STATUS_0.DEV_STATUS = 0x4 (recovery pending)
        i3c_reg_data = 0x4;
        update_device_status(i3c_reg_data);

        // Step 12: Poll ACTIVATE_REC_IMG until == 0xF
        read_image_activation();

        // Step 15: DEV_REC_STATUS = 0x2 (processing image)
        update_recovery_status(0x2);

        // Step 17: Validate image (test: always accept)
        VPRINTF(LOW, "CPTRA: Stage %d image validated\n", stage);

        if (stage < NUM_STAGES - 1) {
            // Intermediate stage cleanup:
            // Clear ACTIVATE_REC_IMG
            update_recovery_ctrl(0x00010000);
            // Reset the indirect FIFO
            reset_indirect_fifo();
            VPRINTF(LOW, "CPTRA: Intermediate stage %d cleanup done\n", stage);
            // Loop continues to step 2 with next stage
        } else {
            // Final stage: recovery successful
            update_recovery_status(0x3); // DEV_REC_STATUS = 0x3
            // DEV_STATUS = 0x1 (device healthy)
            i3c_reg_data = 0x1;
            update_device_status(i3c_reg_data);
            VPRINTF(LOW, "CPTRA: Final stage %d - recovery successful\n", stage);
        }
    }

    VPRINTF(LOW, "CPTRA: All %d stages complete\n", NUM_STAGES);
}

// ============================================================
// main
// ============================================================
void main(void) {

    uint32_t send_payload[4] = {0xabadface, 0xba5eba11, 0xcafebabe, 0xdeadbeef};
    uint32_t read_payload[16];

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " Caliptra AXI 3-Image Streaming Boot\n");
    VPRINTF(LOW, "----------------------------------\n");

    // DMA sanity check
    VPRINTF(LOW, "CPTRA: DMA sanity write to SRAM\n");
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR, 0, send_payload, 16, 0);
    VPRINTF(LOW, "CPTRA: DMA sanity read from SRAM\n");
    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR, 0, read_payload, 16, 0);

    // Sync with MCU is via DEVICE_STATUS_0 = 0x3 (written in recovery_sequence step 2).
    // No READY_FOR_MB_PROCESSING needed.

    VPRINTF(LOW, "CPTRA: Initiating 3-stage Recovery Sequence\n");
    recovery_sequence();
    wait(10000);
}
