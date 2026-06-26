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

#include "mci.h"
#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"
#include "veer-csr.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main(void) {
    VPRINTF(LOW, "==================\nMCI Aggregate Registers Test\n==================\n\n");

    uint32_t reg;
    uint32_t intr_mask;
    // Test FATAL registers
    for (int i=0; i<32 ; i++) {
        VPRINTF(LOW, "Testing FATAL interrupt: %d\n", i);
        // Check that flag is clear
        reg = lsu_read_32(SOC_MCI_TOP_MCI_REG_AGG_ERROR_FATAL);
        if (reg != 0) {
            VPRINTF(LOW, "Expected SOC_MCI_TOP_MCI_REG_AGG_ERROR_FATAL to be: 0, got:%x\n", reg);
            SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
        }

        // Set interrupt
        lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, TB_CMD_INJECT_AGG_ERROR_FATAL_DIRECT | (i << 8));
        for (uint8_t ii = 0; ii < 160; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }

        intr_mask = 1 << i;
        // Check that flag is set
        reg = lsu_read_32(SOC_MCI_TOP_MCI_REG_AGG_ERROR_FATAL);
        if ((reg & intr_mask) == 0) {
            VPRINTF(LOW, "Expected flag to be: %x, got:%x\n", intr_mask, reg);
            SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
        }

        //Writing 0 should not clear it
        lsu_write_32(SOC_MCI_TOP_MCI_REG_AGG_ERROR_FATAL, 0);
        reg = lsu_read_32(SOC_MCI_TOP_MCI_REG_AGG_ERROR_FATAL);
        if ((reg & intr_mask) == 0) {
            VPRINTF(LOW, "Expected flag to be: %x, got:%x\n", intr_mask, reg);
            SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
        }

        //Writing 1 should clear it
        lsu_write_32(SOC_MCI_TOP_MCI_REG_AGG_ERROR_FATAL, intr_mask);
        reg = lsu_read_32(SOC_MCI_TOP_MCI_REG_AGG_ERROR_FATAL);
        if ((reg & intr_mask) != 0) {
            VPRINTF(LOW, "Expected flag to be cleared(0), got:%x\n", reg);
            SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
        }
    }

    // Unmask all NON-FATAL interrupts
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK, 0xFFFFFFFF);
    // Test NON-FATAL registers
    for (int i=0; i<32 ; i++) {
        VPRINTF(LOW, "Testing NON-FATAL interrupt: %d\n", i);
        // Check that flag is clear
        reg = lsu_read_32(SOC_MCI_TOP_MCI_REG_AGG_ERROR_NON_FATAL);
        if (reg != 0) {
            VPRINTF(LOW, "Expected SOC_MCI_TOP_MCI_REG_AGG_ERROR_NON_FATAL to be: 0, got:%x\n", reg);
            SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
        }

        // Set interrupt
        lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, TB_CMD_INJECT_AGG_ERROR_NON_FATAL_DIRECT | (i << 8));
        for (uint8_t ii = 0; ii < 160; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }

        intr_mask = 1 << i;
        // Check that flag is set
        reg = lsu_read_32(SOC_MCI_TOP_MCI_REG_AGG_ERROR_NON_FATAL);
        if ((reg & intr_mask) == 0) {
            VPRINTF(LOW, "Expected flag to be: %x, got:%x\n", intr_mask, reg);
            SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
        }

        //Writing 0 should not clear it
        lsu_write_32(SOC_MCI_TOP_MCI_REG_AGG_ERROR_NON_FATAL, 0);
        reg = lsu_read_32(SOC_MCI_TOP_MCI_REG_AGG_ERROR_NON_FATAL);
        if ((reg & intr_mask) == 0) {
            VPRINTF(LOW, "Expected flag to be: %x, got:%x\n", intr_mask, reg);
            SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
        }

        //Writing 1 should clear it
        lsu_write_32(SOC_MCI_TOP_MCI_REG_AGG_ERROR_NON_FATAL, intr_mask);
        reg = lsu_read_32(SOC_MCI_TOP_MCI_REG_AGG_ERROR_NON_FATAL);
        if ((reg & intr_mask) != 0) {
            VPRINTF(LOW, "Expected flag to be cleared(0), got:%x\n", reg);
            SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
        }
    }

    VPRINTF(LOW, "\nMCI Register Aggregate Tests Completed\n");

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
}
