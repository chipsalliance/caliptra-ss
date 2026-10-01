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

// MCU ROM patch SRAM negative test: LC state that does not allow patching
// (RAW, PROD or RMA, selected by the yml). Caliptra core is still in reset and
// UDS is not provisioned, so the LC gate is the only reason the write can fail.
// The rejected store returns an AXI error, reported by the MCU as a store bus
// error NMI. The test passes from the NMI handler.

#include <stdint.h>

#include "caliptra_ss_lib.h"
#include "printf.h"
#include "riscv-csr.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"

volatile char *stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

#define PATCH_BASE ((uintptr_t)SOC_MCI_TOP_MCU_ROM_PATCH_SRAM_BASE_ADDR)

// addi a0, a0, 0x123
#define PATCH_WORD 0x12350513

// VeeR EL2 NMI cause for an imprecise store bus error
#define MCAUSE_NMI_STORE_BUS_ERR 0xF0000000

static volatile uint32_t expect_nmi = 0;

void nmi_handler(void) {
    uint32_t mcause = csr_read_mcause();

    if (!expect_nmi) {
        handle_error("MCU: Unexpected NMI, mcause 0x%x\n", mcause);
    }
    if (mcause != MCAUSE_NMI_STORE_BUS_ERR) {
        handle_error("MCU: Expected store bus error NMI, got mcause 0x%x\n", mcause);
    }
    VPRINTF(LOW, "MCU: Patch SRAM write rejected in a non-patchable LC state\n");
    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    while (1);
}

void main(void) {
    VPRINTF(LOW, "=================\nMCU: MCU ROM patch SRAM LC negative test\n=================\n");

    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, (uint32_t)nmi_handler);

    expect_nmi = 1;
    lsu_write_32(PATCH_BASE, PATCH_WORD);

    // The store error is imprecise: give the AXI response time to arrive
    mcu_sleep(200);
    handle_error("MCU: Patch SRAM write did not fault in a non-patchable LC state\n");
}
