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
#include "soc_address_map.h"
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "caliptra_ss_lib.h"
#include "riscv-csr.h"
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include "printf.h"
#include "soc_ifc.h"
#include "soc_ifc_ss.h"
#include "caliptra_reg.h"

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Attempt a DWORD write/read as an invalid AXI user; every access must return an
// AXI error. Kept noinline with a single shared message so the ~20 checks below do
// not duplicate code/strings (this Caliptra-core image is ROM-size constrained).
void __attribute__((noinline)) expect_axi_wr_err(uint64_t addr) {
    if (!cptra_axi_dword_write_with_status(addr, xorshift32())) {
        VPRINTF(FATAL, "Caliptra: Expected AXI Error on write @0x%x as invalid user\n", (uint32_t)addr);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }
}

void __attribute__((noinline)) expect_axi_rd_err(uint64_t addr) {
    uint32_t payload[1];
    if (!cptra_axi_dword_read_with_status(addr, payload)) {
        VPRINTF(FATAL, "Caliptra: Expected AXI Error on read @0x%x as invalid user\n", (uint32_t)addr);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }
}

// Test (in conjuction with Caliptra uC C code) exercises invalid AXI and invalid SRAM address access 
// 1. MCU will configure Caliptra uC to be an invalid AXI
// 2. Caliptra uC will attempt CSR and SRAM read writes.  These are expected to return AXI errors

void main(void) {
    uint32_t data;
    uint32_t addr;

    uint32_t mbox_num = decode_single_valid_mbox();

    VPRINTF(LOW, "----------------------------------\nSmoke Test MCI MBOX%x  !!\n----------------------------------\n", mbox_num);
    
    // Do SRAM and CSRs writes and reads and check that AXI errors are returned as expected
    // Writing and read to CSRs
    VPRINTF(LOW, "Caliptra: CSR Writes and Read as Invalid AXI\n");

    // Every mailbox CSR must reject an invalid-AXI-user access with an AXI error.
    // The written data is immaterial (the access is rejected regardless), so a
    // table-driven loop replaces the per-register unrolled blocks.
    static const uint32_t mbox_csr_offsets[] = {
        SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE,
        SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD,
        SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS,
        SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER,
        SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER,
        SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID,
        SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_STATUS,
        SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN,
        SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK,
        SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_HW_STATUS,
    };
    for (uint32_t i = 0; i < sizeof(mbox_csr_offsets) / sizeof(mbox_csr_offsets[0]); i++) {
        uint64_t csr_addr = mbox_csr_offsets[i] + MCU_MBOX_NUM_STRIDE * mbox_num;
        expect_axi_wr_err(csr_addr);
        expect_axi_rd_err(csr_addr);
    }

    for(uint32_t i=0; i<8; i++) {
        data = xorshift32();
        addr = (xorshift32() % 131072)/4;  // Using 128KB
        VPRINTF(LOW, "Caliptra: Write to SRAM[%d]: 0x%x\n", addr, data);
        expect_axi_wr_err(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR + (4*addr) + MCU_MBOX_NUM_STRIDE * mbox_num);

        addr = (xorshift32() % 131072)/4;
        VPRINTF(LOW, "Caliptra: Read from SRAM[%d]\n", addr);
        expect_axi_rd_err(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR + (4*addr) + MCU_MBOX_NUM_STRIDE * mbox_num);
    }

    VPRINTF(LOW, "CALIPTRA: Sequence complete\n");

    SEND_STDOUT_CTRL(0xff);
}
