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

static void expect_read_rejected(uint64_t addr) {
    uint32_t payload[1] = {0};

    VPRINTF(LOW, "Caliptra: Reading MCU ROM patch SRAM 0x%x\n", (uint32_t)addr);
    if (!cptra_axi_dword_read_with_status(addr, payload)) {
        VPRINTF(FATAL, "Caliptra: ERROR Expected DMA ERROR reading MCU ROM patch SRAM 0x%x\n", (uint32_t)addr);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if (payload[0]) {
        VPRINTF(FATAL, "Caliptra: ERROR Expected zero data from MCU ROM patch SRAM 0x%x, got 0x%x\n", (uint32_t)addr, payload[0]);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}

void main(void) {
    VPRINTF(LOW,"----------------------------------\nCaliptra MCU ROM Patch SRAM Checks\n----------------------------------\n");

    // The patch is loaded and reads are open for the MCU, so these fail only
    // because the Caliptra DMA AXI user is not an MCU user.
    expect_read_rejected(PATCH_BASE);
    expect_read_rejected(PATCH_BASE + 4);

    VPRINTF(LOW, "Caliptra: Writing MCU ROM patch SRAM 0x%x\n", (uint32_t)PATCH_BASE);
    if (!cptra_axi_dword_write_with_status(PATCH_BASE, 0xFFFFFFFF)) {
        VPRINTF(FATAL, "Caliptra: ERROR Expected DMA ERROR writing MCU ROM patch SRAM 0x%x\n", (uint32_t)PATCH_BASE);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    VPRINTF(LOW, "Caliptra: TEST PASSED handshake with MCU to finish test\n");
    cptra_mcu_mbox_acquire_lock_set_execute(0, 100);

    cptra_mcu_mbox_wait_for_status(0, 1000, MCU_MBOX_CMD_COMPLETE);
    cptra_mcu_mbox_write_execute(0, 0);

    while(1);
}
