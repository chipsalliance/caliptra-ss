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

// MCU ROM patch SRAM release test (PROD, no patch loaded), MCU side.
// Run 1 (MCU ROM): boot Caliptra core. Caliptra core (cptra_*.c) checks its
//   DMA cannot access the SRAM yet, then sets RESET_REASON and the FW exec
//   region lock, and MCU resets itself into RT.
// Run 2 (MCU RT): the SRAM is released as data memory:
//   - word writes in any order, byte writes (RMW), readback
//   - Caliptra core (non-MCU AXI user) writes/reads it through its DMA
//   - instruction fetch from the released SRAM faults (mcause 1)

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

// Shared with cptra_smoke_test_mcu_rom_patch_sram_release.c
#define MCU_RT_READY_MAGIC 0x5E1EA5ED
#define MCU_WORD0_OFFSET   0x0
#define MCU_WORD0_DATA     0xA5A50000
#define CPTRA_OFFSET       0x40
#define CPTRA_DATA         0xC0FFEE11

#define LAST_OFFSET        0xFFC
#define RMW_OFFSET         0x80
#define FETCH_OFFSET       0xC0
#define RET_INSTR          0x00008067

#define MCAUSE_INSTR_ACCESS_FAULT 0x1

typedef void (*fetch_fn_t)(void);

static volatile uint32_t expect_fetch_fault = 0;

void nmi_handler(void) {
    handle_error("MCU: Unexpected NMI, mcause 0x%x\n", csr_read_mcause());
}

void trap_handler(void) __attribute__((aligned(4)));
void trap_handler(void) {
    uint32_t mcause = csr_read_mcause();
    uint32_t mtval  = csr_read_mtval();

    if (!expect_fetch_fault || mcause != MCAUSE_INSTR_ACCESS_FAULT || mtval != PATCH_BASE + FETCH_OFFSET) {
        handle_error("MCU: Unexpected trap, mcause 0x%x mtval 0x%x\n", mcause, mtval);
    }
    VPRINTF(LOW, "MCU: Fetch from released SRAM faulted\n");
    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    while (1);
}

static void wr_rd_32(uint32_t offset, uint32_t data) {
    uint32_t rd;
    lsu_write_32(PATCH_BASE + offset, data);
    rd = lsu_read_32(PATCH_BASE + offset);
    if (rd != data) {
        handle_error("MCU: Offset 0x%x: exp 0x%x got 0x%x\n", offset, data, rd);
    }
}

static void expect_32(uint32_t offset, uint32_t exp) {
    uint32_t rd = lsu_read_32(PATCH_BASE + offset);
    if (rd != exp) {
        handle_error("MCU: Offset 0x%x: exp 0x%x got 0x%x\n", offset, exp, rd);
    }
}

static void mcu_rt(void) {
    uint32_t cnt;

    VPRINTF(LOW, "MCU: RT, checking released patch SRAM\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, (uint32_t)nmi_handler);
    csr_write_mtvec((uint32_t)trap_handler);

    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_HW_FLOW_STATUS) & MCI_REG_HW_FLOW_STATUS_MCU_ROM_PATCH_ACTIVE_MASK) {
        handle_error("MCU: HW_FLOW_STATUS.mcu_rom_patch_active set without a patch\n");
    }

    // Word writes, not sequential (no write pointer once released)
    wr_rd_32(LAST_OFFSET,      0x0FFC0FFC);
    wr_rd_32(MCU_WORD0_OFFSET, MCU_WORD0_DATA);
    wr_rd_32(CPTRA_OFFSET,     0);
    expect_32(LAST_OFFSET,     0x0FFC0FFC);

    // Partial writes (RMW)
    wr_rd_32(RMW_OFFSET, 0x11223344);
    lsu_write_8(PATCH_BASE + RMW_OFFSET + 1, 0xAA);
    expect_32(RMW_OFFSET, 0x1122AA44);
    lsu_write_8(PATCH_BASE + RMW_OFFSET + 3, 0x55);
    expect_32(RMW_OFFSET, 0x5522AA44);
    if (lsu_read_8(PATCH_BASE + RMW_OFFSET + 2) != 0x22) {
        handle_error("MCU: Byte read mismatch\n");
    }
    VPRINTF(LOW, "MCU: Word and byte accesses OK\n");

    // Caliptra core writes CPTRA_DATA through its DMA
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_FLOW_STATUS, MCU_RT_READY_MAGIC);
    cnt = 0;
    while (lsu_read_32(PATCH_BASE + CPTRA_OFFSET) != CPTRA_DATA) {
        mcu_sleep(64);
        if (++cnt > 2000) {
            handle_error("MCU: Timeout waiting for Caliptra DMA write\n");
        }
    }
    expect_32(MCU_WORD0_OFFSET, MCU_WORD0_DATA);
    VPRINTF(LOW, "MCU: Caliptra DMA write observed\n");

    // Never executable while released
    wr_rd_32(FETCH_OFFSET,     RET_INSTR);
    wr_rd_32(FETCH_OFFSET + 4, RET_INSTR);
    __asm__ volatile ("fence\n\tfence.i" ::: "memory");
    expect_fetch_fault = 1;
    ((fetch_fn_t)(PATCH_BASE + FETCH_OFFSET))();
    handle_error("MCU: Fetch from released SRAM did not fault\n");
}

void main(void) {
    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_RESET_REASON) & MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_MASK) {
        mcu_rt();
    } else {
        VPRINTF(LOW, "=================\nMCU: MCU ROM patch SRAM release test\n=================\n");
        lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, (uint32_t)nmi_handler);

        // MCU ROM: no patch, boot Caliptra core
        mcu_cptra_init_d(.cfg_mcu_fw_sram_exec_reg_size=true, .mcu_fw_sram_exec_reg_size=0x8000);

        VPRINTF(LOW, "MCU: Wait for Caliptra reset req...\n");
        mcu_mci_poll_exec_lock();
        VPRINTF(LOW, "MCU: Observed Caliptra reset req; issuing reset\n");
        mcu_mci_req_reset();
    }
    while (1);
}
