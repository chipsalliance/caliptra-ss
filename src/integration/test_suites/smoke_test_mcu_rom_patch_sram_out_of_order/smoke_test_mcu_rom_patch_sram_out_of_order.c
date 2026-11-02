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

// MCU ROM patch SRAM out-of-order write test (TEST_UNLOCKED1).
// Patch words must be written in order from offset 0. Write words 0 and 1,
// then skip word 2 and write word 3: the write must be rejected (store bus
// error NMI) and must not move the write pointer, so words 2 and 3 can then
// be written in order.

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
#define NUM_WORDS  4
#define REJ_DATA   0xBADBAD03

// VeeR EL2 NMI cause for an imprecise store bus error
#define MCAUSE_NMI_STORE_BUS_ERR 0xF0000000

static const uint32_t k_data[NUM_WORDS] = { 0x11111100, 0x22222201, 0x33333302, 0x44444403 };

static volatile uint32_t expect_nmi = 0;

void nmi_handler(void) {
    uint32_t mcause = csr_read_mcause();

    // A second NMI means the in-order writes below were rejected
    if (!expect_nmi) {
        handle_error("MCU: Unexpected NMI, mcause 0x%x\n", mcause);
    }
    expect_nmi = 0;
    if (mcause != MCAUSE_NMI_STORE_BUS_ERR) {
        handle_error("MCU: Expected store bus error NMI, got mcause 0x%x\n", mcause);
    }
    VPRINTF(LOW, "MCU: Out-of-order patch write was rejected\n");

    // The rejected write did not move the write pointer
    lsu_write_32(PATCH_BASE + 8,  k_data[2]);
    lsu_write_32(PATCH_BASE + 12, k_data[3]);
    for (uint32_t i = 0; i < NUM_WORDS; i++) {
        uint32_t rd = lsu_read_32(PATCH_BASE + 4 * i);
        if (rd != k_data[i]) {
            handle_error("MCU: Patch word %d: exp 0x%x got 0x%x\n", i, k_data[i], rd);
        }
    }
    VPRINTF(LOW, "MCU: In-order writes after the rejected write OK\n");
    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    while (1);
}

void main(void) {
    VPRINTF(LOW, "=================\nMCU: MCU ROM patch SRAM out-of-order write test\n=================\n");

    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, (uint32_t)nmi_handler);

    // In-order writes while Caliptra core is still in reset
    lsu_write_32(PATCH_BASE + 0, k_data[0]);
    lsu_write_32(PATCH_BASE + 4, k_data[1]);
    for (uint32_t i = 0; i < 2; i++) {
        if (lsu_read_32(PATCH_BASE + 4 * i) != k_data[i]) {
            handle_error("MCU: Patch word %d readback mismatch\n", i);
        }
    }

    // Skip word 2
    expect_nmi = 1;
    lsu_write_32(PATCH_BASE + 12, REJ_DATA);
    for (uint32_t i = 0; i < 100; i++) {
        if (lsu_read_32(PATCH_BASE) != k_data[0]) {
            handle_error("MCU: Patch word 0 changed\n");
        }
    }
    handle_error("MCU: Out-of-order patch write did not fault\n");
}
