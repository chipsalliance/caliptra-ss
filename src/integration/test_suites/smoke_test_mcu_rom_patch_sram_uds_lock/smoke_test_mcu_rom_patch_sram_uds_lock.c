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

// MCU ROM patch SRAM UDS/FE test (DEV, non-debug).
//   1. Program one UDS word and one FE word without a digest (the partitions
//      stay unlocked) and re-init the fuse controller so they are broadcast.
//   2. Load the patch and boot Caliptra core.
//   3. TB check: fuses hold non-zero UDS/FE, but Caliptra core sees zeros.
//   4. Writes to blank UDS/FE words are now discarded by the fuse controller
//      filter.

#include <stdint.h>

#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "fuse_ctrl_mmap.h"
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

#define SECRET_GRANULARITY 64

typedef uint32_t (*patch_fn_t)(uint32_t);

void nmi_handler(void) {
    handle_error("MCU: Unexpected NMI, mcause 0x%x\n", csr_read_mcause());
}

static void load_patch(void) {
    for (uint32_t i = 0; i < PATCH_FILL_WORDS; i++) {
        lsu_write_32(PATCH_BASE + 4 * i, (i < PATCH_WORDS) ? k_patch[i] : 0);
    }
    for (uint32_t i = 0; i < PATCH_WORDS; i++) {
        if (lsu_read_32(PATCH_BASE + 4 * i) != k_patch[i]) {
            handle_error("MCU: Patch word %d readback mismatch\n", i);
        }
    }
}

static void run_patch(const char *tag) {
    patch_fn_t fn = (patch_fn_t)PATCH_BASE;
    uint32_t   rv;

    __asm__ volatile ("fence\n\tfence.i" ::: "memory");
    rv = fn(PATCH_ARG);
    if (rv != PATCH_EXP) {
        handle_error("MCU: [%s] patch returned 0x%x, exp 0x%x\n", tag, rv, PATCH_EXP);
    }
    VPRINTF(LOW, "MCU: [%s] patch executed OK\n", tag);
}

static void secret_write(uint32_t addr, uint32_t exp_status, const char *msg) {
    if (!dai_wr(addr, 0xA5A5A5A5, 0x5A5A5A5A, SECRET_GRANULARITY, exp_status)) {
        handle_error("MCU: %s: DAI write to 0x%x status mismatch\n", msg, addr);
    }
}

void main(void) {
    VPRINTF(LOW, "=================\nMCU: MCU ROM patch SRAM UDS/FE test\n=================\n");

    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, (uint32_t)nmi_handler);
    wait_dai_op_idle(0);

    // 1. Unpatched: Caliptra-identity writes to UDS/FE succeed. No digest.
    grant_caliptra_core_for_fc_writes();
    secret_write(CPTRA_CORE_UDS_SEED, 0, "UDS write before patch");
    secret_write(CPTRA_CORE_FIELD_ENTROPY_0, 0, "FE write before patch");
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // 2. Load the patch while Caliptra core is in reset, then boot Caliptra core
    load_patch();
    run_patch("before Caliptra boot");
    mcu_cptra_init_d();
    run_patch("after Caliptra boot");

    // 3. Caliptra core must have captured zero UDS/FE
    SEND_STDOUT_CTRL(CMD_MCU_ROM_PATCH_EXPECT_UDS_FE_ZEROIZED);
    mcu_sleep(100);

    // 4. Blank UDS/FE words: only the patch rule in the filter can reject these.
    //    The same Caliptra-identity writes succeeded in step 1, before the patch.
    grant_caliptra_core_for_fc_writes();
    secret_write(CPTRA_CORE_UDS_SEED + 8, OTP_CTRL_STATUS_DAI_ERROR_MASK, "UDS write with patch");
    secret_write(CPTRA_CORE_FIELD_ENTROPY_0 + 8, OTP_CTRL_STATUS_DAI_ERROR_MASK, "FE write with patch");
    revoke_grant_mcu_for_fc_writes();

    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
}
