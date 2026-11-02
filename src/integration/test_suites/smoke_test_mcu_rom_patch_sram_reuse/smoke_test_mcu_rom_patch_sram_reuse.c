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

// MCU ROM patch SRAM reuse test (TEST_UNLOCKED1), MCU side.
// The patch loaded by MCU ROM at cold boot stays usable for the rest of the
// power cycle, and HW_FLOW_STATUS.mcu_rom_patch_active reports it.
// Run 1 (cold boot, MCU ROM): flag clear, load the patch, flag set, run it,
//   boot Caliptra core. Caliptra core (cptra_*.c) hands off to MCU RT.
// Run 2 (MCU RT FW): flag set, patch readable and executable, then warm reset.
// Run 3 (warm reset, MCU ROM): flag still set, run the patch without
//   reloading it.

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

// Zero-fill past the patch so IFU prefetch never reads beyond the write pointer.
#define PATCH_FILL_WORDS 8
#define PATCH_ARG        0x1000
#define PATCH_EXP        (PATCH_ARG + 0x123)

typedef uint32_t (*patch_fn_t)(uint32_t);

void nmi_handler(void) {
    handle_error("MCU: Unexpected NMI, mcause 0x%x\n", csr_read_mcause());
}

static void expect_patch_flag(uint32_t exp, const char *tag) {
    uint32_t flag = (lsu_read_32(SOC_MCI_TOP_MCI_REG_HW_FLOW_STATUS) &
                     MCI_REG_HW_FLOW_STATUS_MCU_ROM_PATCH_ACTIVE_MASK) ? 1 : 0;
    if (flag != exp) {
        handle_error("MCU: [%s] HW_FLOW_STATUS.mcu_rom_patch_active exp %d got %d\n", tag, exp, flag);
    }
    VPRINTF(LOW, "MCU: [%s] mcu_rom_patch_active = %d\n", tag, flag);
}

static void check_and_run_patch(const char *tag) {
    patch_fn_t fn = (patch_fn_t)PATCH_BASE;
    uint32_t   rv;

    for (uint32_t i = 0; i < PATCH_WORDS; i++) {
        uint32_t rd = lsu_read_32(PATCH_BASE + 4 * i);
        if (rd != k_patch[i]) {
            handle_error("MCU: [%s] patch word %d: exp 0x%x got 0x%x\n", tag, i, k_patch[i], rd);
        }
    }
    __asm__ volatile ("fence\n\tfence.i" ::: "memory");
    rv = fn(PATCH_ARG);
    if (rv != PATCH_EXP) {
        handle_error("MCU: [%s] patch returned 0x%x, exp 0x%x\n", tag, rv, PATCH_EXP);
    }
    VPRINTF(LOW, "MCU: [%s] patch readback and execution OK\n", tag);
}

void main(void) {
    uint32_t reset_reason = lsu_read_32(SOC_MCI_TOP_MCI_REG_RESET_REASON);

    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, (uint32_t)nmi_handler);

    if (reset_reason & MCI_REG_RESET_REASON_WARM_RESET_MASK) {
        // Run 3: MCU ROM after warm reset uses the patch loaded at cold boot
        expect_patch_flag(1, "warm reset");
        check_and_run_patch("warm reset");
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    } else if (reset_reason & MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_MASK) {
        // Run 2: MCU RT FW calls the patched function
        expect_patch_flag(1, "MCU RT");
        check_and_run_patch("MCU RT");
        VPRINTF(LOW, "MCU: Requesting warm reset\n");
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
    } else {
        // Run 1: MCU ROM at cold boot
        VPRINTF(LOW, "=================\nMCU: MCU ROM patch SRAM reuse test\n=================\n");
        expect_patch_flag(0, "cold boot, before load");
        for (uint32_t i = 0; i < PATCH_FILL_WORDS; i++) {
            lsu_write_32(PATCH_BASE + 4 * i, (i < PATCH_WORDS) ? k_patch[i] : 0);
        }
        expect_patch_flag(1, "cold boot, after load");
        check_and_run_patch("cold boot");

        mcu_cptra_init_d(.cfg_mcu_fw_sram_exec_reg_size=true, .mcu_fw_sram_exec_reg_size=0x8000);

        VPRINTF(LOW, "MCU: Wait for Caliptra reset req...\n");
        mcu_mci_poll_exec_lock();
        VPRINTF(LOW, "MCU: Observed Caliptra reset req; issuing reset\n");
        mcu_mci_req_reset();
    }
    while (1);
}
