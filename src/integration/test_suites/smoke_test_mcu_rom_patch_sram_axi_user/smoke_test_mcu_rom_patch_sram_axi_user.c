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

// MCU ROM patch SRAM AXI user test (TEST_UNLOCKED1), MCU side.
// MCU loads the patch and boots Caliptra core. Caliptra core then tries to read
// and write the patch SRAM through its AXI DMA (cptra_*.c) and expects AXI
// errors. Reads are still open for the MCU at that point, so a rejected
// Caliptra read proves the AXI user check. The MCU finally checks the patch is
// unchanged and still executable.

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

typedef uint32_t (*patch_fn_t)(uint32_t);

void nmi_handler(void) {
    handle_error("MCU: Unexpected NMI, mcause 0x%x\n", csr_read_mcause());
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

    __asm__ volatile ("fence\n\tfence.i" ::: "memory");
    rv = fn(PATCH_ARG);
    if (rv != PATCH_EXP) {
        handle_error("MCU: [%s] patch returned 0x%x, exp 0x%x\n", tag, rv, PATCH_EXP);
    }
    VPRINTF(LOW, "MCU: [%s] patch executed OK\n", tag);
}

void main(void) {
    uint32_t axi_select = xorshift32() % 5;
    uint32_t axi_user_id[] = { xorshift32(), xorshift32(), xorshift32(), xorshift32(), xorshift32() };
    uint32_t caliptra_dma_axi_user = axi_user_id[axi_select];

    VPRINTF(LOW, "=================\nMCU: MCU ROM patch SRAM AXI user test\n=================\n");

    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, (uint32_t)nmi_handler);

    // 1. ROM flow: load the patch while Caliptra core is still in reset
    load_patch();
    check_patch("before Caliptra boot");
    run_patch("before Caliptra boot");

    // 2. Boot Caliptra core with a DMA AXI user that can use MCU mailbox 0
    VPRINTF(LOW, "MCU: Caliptra DMA AXI USER 0x%x\n", caliptra_dma_axi_user);
    mcu_mbox_clear_lock_out_of_reset(0);
    mcu_mbox_configure_valid_axi(0, axi_user_id);
    mcu_cptra_init_d(.cfg_cptra_dma_axi_user=true, .cptra_dma_axi_user=caliptra_dma_axi_user);

    // 3. Caliptra core reports its DMA checks through mailbox 0
    VPRINTF(LOW, "MCU: Waiting on Caliptra to finish\n");
    if (!mcu_mbox_wait_for_user_execute(0, 1, 10000)) {
        handle_error("MCU: Mbox0 Caliptra did not set execute\n");
    }
    mcu_mbox_update_status(0, MCU_MBOX_CMD_COMPLETE);
    if (!mcu_mbox_wait_for_user_execute(0, 0, 10000)) {
        handle_error("MCU: Mbox0 Caliptra did not clear execute\n");
    }

    // 4. The patch is unchanged and still executable by the MCU
    check_patch("after Caliptra DMA");
    run_patch("after Caliptra DMA");

    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
}
