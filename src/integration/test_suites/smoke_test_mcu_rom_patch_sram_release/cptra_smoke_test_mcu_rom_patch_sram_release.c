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
// MCU ROM patch SRAM release test, Caliptra core side.
// Before MCU RT FW runs, the patch SRAM is closed to the Caliptra DMA AXI user.
// Caliptra core then hands off to MCU RT (RESET_REASON + FW exec region lock),
// waits for MCU RT to signal through FW_FLOW_STATUS, and writes/reads the
// released SRAM through its DMA.
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "soc_ifc.h"
#include "soc_ifc_ss.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile uint32_t  intr_count;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define PATCH_BASE ((uint64_t)SOC_MCI_TOP_MCU_ROM_PATCH_SRAM_BASE_ADDR)

// Shared with smoke_test_mcu_rom_patch_sram_release.c
#define MCU_RT_READY_MAGIC 0x5E1EA5ED
#define MCU_WORD0_OFFSET   0x0
#define MCU_WORD0_DATA     0xA5A50000
#define CPTRA_OFFSET       0x40
#define CPTRA_DATA         0xC0FFEE11

static void fail(const char *msg, uint32_t val) {
    VPRINTF(FATAL, "Caliptra: ERROR %s 0x%x\n", msg, val);
    SEND_STDOUT_CTRL(0x1);
    while(1);
}

void main(void) {
    uint32_t data;
    uint32_t cnt;

    VPRINTF(LOW,"----------------------------------\nCaliptra MCU ROM Patch SRAM Release\n----------------------------------\n");

    // Not released before MCU RT FW runs
    data = 0;
    if (!cptra_axi_dword_read_with_status(PATCH_BASE, &data)) {
        fail("Expected DMA ERROR reading patch SRAM before release, data", data);
    }
    if (!cptra_axi_dword_write_with_status(PATCH_BASE + CPTRA_OFFSET, CPTRA_DATA)) {
        fail("Expected DMA ERROR writing patch SRAM before release, addr", (uint32_t)(PATCH_BASE + CPTRA_OFFSET));
    }
    VPRINTF(LOW, "Caliptra: Patch SRAM closed before MCU RT\n");

    // Hand off to MCU RT FW
    if (cptra_axi_dword_write_with_status(SOC_MCI_TOP_MCI_REG_RESET_REASON, MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_MASK)) {
        fail("DMA ERROR writing RESET_REASON", 0);
    }
    lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0, 0x4);

    // Wait for MCU RT to initialize the SRAM
    cnt = 0;
    do {
        data = 0;
        if (cptra_axi_dword_read_with_status(SOC_MCI_TOP_MCI_REG_FW_FLOW_STATUS, &data)) {
            fail("DMA ERROR reading FW_FLOW_STATUS", 0);
        }
        if (++cnt > 10000) {
            fail("Timeout waiting for MCU RT, FW_FLOW_STATUS", data);
        }
    } while (data != MCU_RT_READY_MAGIC);

    // Released: any AXI user can read and write
    data = 0;
    if (cptra_axi_dword_read_with_status(PATCH_BASE + MCU_WORD0_OFFSET, &data)) {
        fail("DMA ERROR reading released patch SRAM", 0);
    }
    if (data != MCU_WORD0_DATA) {
        fail("Released patch SRAM read mismatch, got", data);
    }
    if (cptra_axi_dword_write_with_status(PATCH_BASE + CPTRA_OFFSET, CPTRA_DATA)) {
        fail("DMA ERROR writing released patch SRAM", 0);
    }
    data = 0;
    if (cptra_axi_dword_read_with_status(PATCH_BASE + CPTRA_OFFSET, &data) || data != CPTRA_DATA) {
        fail("Released patch SRAM readback mismatch, got", data);
    }
    VPRINTF(LOW, "Caliptra: Released patch SRAM DMA write/read OK\n");

    while(1);
}
