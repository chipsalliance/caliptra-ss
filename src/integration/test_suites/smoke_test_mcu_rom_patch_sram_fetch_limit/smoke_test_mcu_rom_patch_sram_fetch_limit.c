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

// MCU ROM patch SRAM fetch limit test (TEST_UNLOCKED1).
// Only words written by MCU ROM in this power cycle (below the write pointer)
// can be fetched or read, so stale or preloaded SRAM content never executes.
// Load an 8-word patch and run it, then:
//   1. fetch from word 8 -> instruction access fault (mcause 1)
//   2. LSU read of word 8 -> load access fault (mcause 5) or load bus error
//      NMI (mcause 0xF0000001)

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

// Patch: uint32_t patch_fn(uint32_t x) { return x + 0x123; }
#define PATCH_WORDS 2
static const uint32_t k_patch[PATCH_WORDS] = { 0x12350513, 0x00008067 };

#define PATCH_FILL_WORDS 8
#define PATCH_ARG        0x1000
#define PATCH_EXP        (PATCH_ARG + 0x123)
#define BEYOND_ADDR      (PATCH_BASE + 4 * PATCH_FILL_WORDS)

#define MCAUSE_INSTR_ACCESS_FAULT 0x1
#define MCAUSE_LOAD_ACCESS_FAULT  0x5
#define MCAUSE_NMI_LOAD_BUS_ERR   0xF0000001

typedef uint32_t (*patch_fn_t)(uint32_t);

enum { STAGE_NONE, STAGE_FETCH, STAGE_LOAD };
static volatile uint32_t stage = STAGE_NONE;

static void check_load_fault(uint32_t mcause) {
    if (stage != STAGE_LOAD) {
        handle_error("MCU: Unexpected trap/NMI, mcause 0x%x, stage %d\n", mcause, stage);
    }
    VPRINTF(LOW, "MCU: Read beyond the write pointer faulted, mcause 0x%x\n", mcause);
    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    while (1);
}

void nmi_handler(void) {
    uint32_t mcause = csr_read_mcause();

    if (mcause != MCAUSE_NMI_LOAD_BUS_ERR) {
        handle_error("MCU: Unexpected NMI, mcause 0x%x\n", mcause);
    }
    check_load_fault(mcause);
}

void trap_handler(void) __attribute__((aligned(4)));
void trap_handler(void) {
    uint32_t mcause = csr_read_mcause();
    uint32_t mtval  = csr_read_mtval();

    if (mcause == MCAUSE_LOAD_ACCESS_FAULT) {
        check_load_fault(mcause);
    }
    if (stage != STAGE_FETCH || mcause != MCAUSE_INSTR_ACCESS_FAULT || mtval != BEYOND_ADDR) {
        handle_error("MCU: Unexpected trap, mcause 0x%x mtval 0x%x stage %d\n", mcause, mtval, stage);
    }
    VPRINTF(LOW, "MCU: Fetch beyond the write pointer faulted\n");

    stage = STAGE_LOAD;
    if (lsu_read_32(BEYOND_ADDR)) {
        VPRINTF(LOW, "MCU: Read beyond the write pointer returned data\n");
    }
    for (uint32_t i = 0; i < 100; i++) {
        lsu_read_32(PATCH_BASE);
    }
    handle_error("MCU: Read beyond the write pointer did not fault\n");
}

void main(void) {
    patch_fn_t fn;
    uint32_t   rv;

    VPRINTF(LOW, "=================\nMCU: MCU ROM patch SRAM fetch limit test\n=================\n");

    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, (uint32_t)nmi_handler);
    csr_write_mtvec((uint32_t)trap_handler);

    for (uint32_t i = 0; i < PATCH_FILL_WORDS; i++) {
        lsu_write_32(PATCH_BASE + 4 * i, (i < PATCH_WORDS) ? k_patch[i] : 0);
    }
    __asm__ volatile ("fence\n\tfence.i" ::: "memory");

    fn = (patch_fn_t)PATCH_BASE;
    rv = fn(PATCH_ARG);
    if (rv != PATCH_EXP) {
        handle_error("MCU: Patch returned 0x%x, exp 0x%x\n", rv, PATCH_EXP);
    }
    VPRINTF(LOW, "MCU: Patch executed OK\n");

    stage = STAGE_FETCH;
    fn = (patch_fn_t)BEYOND_ADDR;
    fn(PATCH_ARG);
    handle_error("MCU: Fetch beyond the write pointer did not fault\n");
}
