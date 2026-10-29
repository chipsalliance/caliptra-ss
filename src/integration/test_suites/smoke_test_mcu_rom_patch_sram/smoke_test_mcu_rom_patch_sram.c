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

// MCU ROM patch SRAM positive test (LC state TEST_UNLOCKED1, TEST_LOCKED1 or DEV,
// selected by the yml).
// Mimics MCU ROM: load a patch while Caliptra core is still in reset, read it
// back and execute it, then boot Caliptra and check the patch is still
// executable but no longer writable.

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
//   addi a0, a0, 0x123
//   ret
#define PATCH_WORDS 2
static const uint32_t k_patch[PATCH_WORDS] = { 0x12350513, 0x00008067 };

// Zero-fill past the patch so IFU prefetch never reads uninitialized SRAM.
#define PATCH_FILL_WORDS 8
#define PATCH_ARG        0x1000
#define PATCH_EXP        (PATCH_ARG + 0x123)
#define LOCK_TEST_DATA   0xDEADBEEF

// VeeR EL2 NMI cause for an imprecise store bus error
#define MCAUSE_NMI_STORE_BUS_ERR 0xF0000000

typedef uint32_t (*patch_fn_t)(uint32_t);

static volatile uint32_t expect_lock_nmi = 0;

void nmi_handler(void) {
    uint32_t mcause = csr_read_mcause();

    if (!expect_lock_nmi) {
        handle_error("MCU: Unexpected NMI, mcause 0x%x\n", mcause);
    }
    if (mcause != MCAUSE_NMI_STORE_BUS_ERR) {
        handle_error("MCU: Expected store bus error NMI, got mcause 0x%x\n", mcause);
    }
    if (lsu_read_32(PATCH_BASE) != k_patch[0]) {
        handle_error("MCU: Locked patch SRAM was modified\n");
    }
    VPRINTF(LOW, "MCU: Patch SRAM write after Caliptra boot was rejected\n");
    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    while (1);
}

static void load_patch(void) {
    for (uint32_t i = 0; i < PATCH_FILL_WORDS; i++) {
        lsu_write_32(PATCH_BASE + 4 * i, (i < PATCH_WORDS) ? k_patch[i] : 0);
    }
}

static void check_patch(const char *tag) {
    for (uint32_t i = 0; i < PATCH_WORDS; i++) {
        uint32_t rd = lsu_read_32(PATCH_BASE + 4 * i);
        if (rd != k_patch[i]) {
            handle_error("MCU: [%s] patch word %d: exp 0x%x got 0x%x\n", tag, i, k_patch[i], rd);
        }
    }
    VPRINTF(LOW, "MCU: [%s] patch readback OK\n", tag);
}

static void run_patch(const char *tag) {
    patch_fn_t fn = (patch_fn_t)PATCH_BASE;
    uint32_t   rv;

    // Make sure the patch stores are complete before fetching from the SRAM
    __asm__ volatile ("fence\n\tfence.i" ::: "memory");
    rv = fn(PATCH_ARG);
    if (rv != PATCH_EXP) {
        handle_error("MCU: [%s] patch returned 0x%x, exp 0x%x\n", tag, rv, PATCH_EXP);
    }
    VPRINTF(LOW, "MCU: [%s] patch executed OK\n", tag);
}

void main(void) {
    VPRINTF(LOW, "=================\nMCU: MCU ROM patch SRAM test\n=================\n");

    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, (uint32_t)nmi_handler);

    // 1. ROM flow: load the patch while Caliptra core is still in reset
    load_patch();
    check_patch("before Caliptra boot");
    run_patch("before Caliptra boot");

    // 2. Boot Caliptra: the patch stays readable/executable
    mcu_cptra_init_d();
    check_patch("after Caliptra boot");
    run_patch("after Caliptra boot");

    // 3. Write lock: the write is rejected with an AXI error (store bus error NMI)
    expect_lock_nmi = 1;
    lsu_write_32(PATCH_BASE, LOCK_TEST_DATA);
    for (uint32_t i = 0; i < 100; i++) {
        if (lsu_read_32(PATCH_BASE) != k_patch[0]) {
            handle_error("MCU: Patch SRAM was writable after Caliptra boot\n");
        }
    }
    handle_error("MCU: Write to locked patch SRAM did not fault\n");
}
