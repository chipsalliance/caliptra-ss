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
#include "caliptra_defines.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include <stdint.h>
#include "printf.h"
#include "caliptra_isr.h"
#include "soc_address_map.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity             verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity             verbosity_g = MEDIUM;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// FIXME soc_ifc addr width is 19-bits, use a param here
#define SOC_IFC_ADDR_WIDTH_MASK ((1 << 19) - 1)
// FIXME mci addr width is 24-bits, use a param here
#define MCI_ADDR_WIDTH_MASK ((1 << 24) - 1)

inline void cpt_sleep (const uint32_t cycles) {
    for (uint8_t ii = 0; ii < cycles; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
}

void sha_accel_acquire_lock(uint64_t base_addr) {
    uint32_t cnt = 0;
    uint32_t data = 0;
    VPRINTF(MEDIUM, "FW: Acquire SHA Lock\n");
    soc_ifc_axi_dma_read_ahb_payload(base_addr + SHA512_ACC_CSR_LOCK, 0, &data, 4, 0);
    while((data & SHA512_ACC_CSR_LOCK_LOCK_MASK) == 1) {
        if (cnt++ > 100) {
            VPRINTF(FATAL, "FW: Failed to acquire SHA Lock via AXI after 100 attempts!\n")
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        cpt_sleep(32);
        soc_ifc_axi_dma_read_ahb_payload(base_addr + SHA512_ACC_CSR_LOCK, 0, &data, 4, 0);
    }
}

void sha_accel_set_cmd(uint64_t base_addr, enum sha_accel_mode_e mode, uint32_t dlen) {
    uint32_t reg;
    reg = (mode << SHA512_ACC_CSR_MODE_MODE_LOW) & SHA512_ACC_CSR_MODE_MODE_MASK;
    VPRINTF(MEDIUM, "FW: Set SHA command\n");
    soc_ifc_axi_dma_send_ahb_payload(base_addr + SHA512_ACC_CSR_MODE, 0, &reg, 4, 0);
    soc_ifc_axi_dma_send_ahb_payload(base_addr + SHA512_ACC_CSR_DLEN, 0, &dlen, 4, 0);
}

void sha_accel_push_datain(uint64_t mcu_sram_addr, uint64_t sha_acc_addr, uint32_t dlen) {
    uint32_t dlen_padded;
    VPRINTF(MEDIUM, "FW: Arm transfer to SHA DATAIN\n");
    if (dlen & 0x3) {
        dlen_padded = dlen + (4 - (dlen & 0x3));
        VPRINTF(HIGH, "FW: DLEN (0x%x) is not aligned to dw-size, padding DLEN to 0x%x\n", dlen, dlen_padded);
    } else {
        dlen_padded = dlen;
    }
    soc_ifc_axi_dma_send_axi_to_axi(mcu_sram_addr + 0x400, 0, sha_acc_addr + SHA512_ACC_CSR_DATAIN, 1, dlen_padded, 0);
}

void sha_accel_execute(uint64_t base_addr) {
    uint32_t reg = 1;
    VPRINTF(MEDIUM, "FW: Set SHA execute\n");
    soc_ifc_axi_dma_send_ahb_payload(base_addr + SHA512_ACC_CSR_EXECUTE, 0, &reg, 4, 0);
}

void sha_accel_poll_status(uint64_t base_addr) {
    uint32_t cnt = 0;
    uint32_t sts;
    VPRINTF(MEDIUM, "FW: Poll SHA status\n");
    soc_ifc_axi_dma_read_ahb_payload(base_addr + SHA512_ACC_CSR_STATUS, 0, &sts, 4, 0);
    while ((sts & SHA512_ACC_CSR_STATUS_VALID_MASK) != SHA512_ACC_CSR_STATUS_VALID_MASK) {
        if (cnt++ > 10000) {
            VPRINTF(FATAL, "FW: SHA accel failed to report digest valid after 10000 attempts!\n")
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        cpt_sleep(32);
        soc_ifc_axi_dma_read_ahb_payload(base_addr + SHA512_ACC_CSR_STATUS, 0, &sts, 4, 0);
    }
}

void sha_accel_read_result(uint64_t base_addr, uint8_t dw_cnt, uint32_t * digest) {
    VPRINTF(MEDIUM, "FW: Read SHA Digest\n");
    soc_ifc_axi_dma_read_ahb_payload(base_addr + SHA512_ACC_CSR_DIGEST_0, 0, digest, dw_cnt << 2, 0);
}

uint8_t sha_accel_check_result(uint8_t dw_cnt, uint32_t * digest, uint32_t * exp_digest) {
    uint8_t match = 1;
    VPRINTF(MEDIUM, "FW: Compare SHA Digest with Expected\n");
    for (uint8_t ii = 0; ii < dw_cnt; ii++) {
        if (digest[ii] != exp_digest[ii]) {
            VPRINTF(ERROR, "DIGEST MISMATCH ERROR [%d]: Actual digest (0x%x) != expected (0x%x)\n", ii, digest[ii], exp_digest[ii]);
            match = 0;
        } else {
            VPRINTF(HIGH, "DIGEST [%d] MATCH: actual (0x%x) expected (0x%x)\n", ii, digest[ii], exp_digest[ii]);
        }
    }
    return match;
}

void sha_accel_clr_lock(uint64_t base_addr) {
    uint32_t reg = SHA512_ACC_CSR_LOCK_LOCK_MASK;
    VPRINTF(MEDIUM, "FW: Clear SHA Lock\n");
    soc_ifc_axi_dma_send_ahb_payload(base_addr + SHA512_ACC_CSR_LOCK, 0, &reg, 4, 0);
}

void main () {

    uint32_t ii;
    uint32_t data;
    uint32_t mode; // 0 = sha384, 1 = sha512
    uint32_t dlen; // bytes
    uint32_t digest[16];
    uint32_t exp_digest[16]; // expected result
    uint8_t  test_pass = 1;

    uint64_t sha_acc_addr;
    uint64_t mcu_sram_addr;

    // Message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " Caliptra SHA Acc (in CSS)!!\n"      );
    VPRINTF(LOW, "----------------------------------\n");

    // Get base addresses for AXI MAP from strap inputs
    sha_acc_addr = ((uint64_t) lsu_read_32(CLP_SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_H) << 32) |
                   ((uint64_t) lsu_read_32(CLP_SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_L));
    sha_acc_addr += CLP_SHA512_ACC_CSR_BASE_ADDR & SOC_IFC_ADDR_WIDTH_MASK;

    mcu_sram_addr = ((uint64_t) lsu_read_32(CLP_SOC_IFC_REG_SS_MCI_BASE_ADDR_H) << 32) |
                    ((uint64_t) lsu_read_32(CLP_SOC_IFC_REG_SS_MCI_BASE_ADDR_L));
    mcu_sram_addr += SOC_MCI_TOP_MCU_SRAM_BASE_ADDR & MCI_ADDR_WIDTH_MASK;

    // Read parameters for SHA test case to run
    soc_ifc_axi_dma_read_ahb_payload(mcu_sram_addr + 0    , 0, &mode     ,  4, 0);
    soc_ifc_axi_dma_read_ahb_payload(mcu_sram_addr + 4    , 0, &dlen     ,  4, 0);
    soc_ifc_axi_dma_read_ahb_payload(mcu_sram_addr + 0x100, 0, exp_digest, 64, 0); // MSB stored to index 0, which matches how we'll read the result later
    VPRINTF(LOW, "FW: Running sha accel test with SHA512_mode: %d dlen: 0x%x\n", mode, dlen);
    VPRINTF(HIGH, "FW: Exp Digest [%d]: 0x%x\n", 0 , exp_digest[0]);
    VPRINTF(HIGH, "FW: Exp Digest [%d]: 0x%x\n", 1 , exp_digest[1]);
    VPRINTF(HIGH, "FW: Exp Digest [%d]: 0x%x\n", 2 , exp_digest[2]);
    VPRINTF(HIGH, "FW: Exp Digest [%d]: 0x%x\n", 3 , exp_digest[3]);
    VPRINTF(HIGH, "FW: Exp Digest [%d]: 0x%x\n", 4 , exp_digest[4]);
    VPRINTF(HIGH, "FW: Exp Digest [%d]: 0x%x\n", 5 , exp_digest[5]);
    VPRINTF(HIGH, "FW: Exp Digest [%d]: 0x%x\n", 6 , exp_digest[6]);
    VPRINTF(HIGH, "FW: Exp Digest [%d]: 0x%x\n", 7 , exp_digest[7]);
    VPRINTF(HIGH, "FW: Exp Digest [%d]: 0x%x\n", 8 , exp_digest[8]);
    VPRINTF(HIGH, "FW: Exp Digest [%d]: 0x%x\n", 9 , exp_digest[9]);
    VPRINTF(HIGH, "FW: Exp Digest [%d]: 0x%x\n", 10, exp_digest[10]);
    VPRINTF(HIGH, "FW: Exp Digest [%d]: 0x%x\n", 11, exp_digest[11]);
    if (mode) {
        VPRINTF(HIGH, "FW: Exp Digest [%d]: 0x%x\n", 12, exp_digest[12]);
        VPRINTF(HIGH, "FW: Exp Digest [%d]: 0x%x\n", 13, exp_digest[13]);
        VPRINTF(HIGH, "FW: Exp Digest [%d]: 0x%x\n", 14, exp_digest[14]);
        VPRINTF(HIGH, "FW: Exp Digest [%d]: 0x%x\n", 15, exp_digest[15]);
    }

    // Release lock, as Caliptra comes out of reset with lock=1
    soc_ifc_sha_accel_clr_lock();

    // Run SHA Accelerator protocol via AXI using DMA assist
                sha_accel_acquire_lock(sha_acc_addr                                              );
                sha_accel_set_cmd     (sha_acc_addr, mode ? SHA_STREAM_512 : SHA_STREAM_384, dlen);
                sha_accel_push_datain (mcu_sram_addr, sha_acc_addr, dlen                         );
                sha_accel_execute     (sha_acc_addr                                              );
                sha_accel_poll_status (sha_acc_addr                                              );
                sha_accel_read_result (sha_acc_addr, mode ? 16 : 12, digest                      );
    test_pass = sha_accel_check_result(mode ? 16 : 12, digest, exp_digest                        );
                sha_accel_clr_lock    (sha_acc_addr                                              );

    // Report result and end sim
    if (test_pass) {
        VPRINTF(LOW, "SHA accelerator test (via DMA) passed - full digest matched expected!\n");
    } else {
        VPRINTF(LOW, "SHA accelerator test (via DMA) failed\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}
