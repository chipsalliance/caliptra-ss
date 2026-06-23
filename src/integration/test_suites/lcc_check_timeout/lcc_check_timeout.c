//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
//
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
//********************************************************************************
//
// Test: lcc_check_timeout
//
// Verifies that LSFR timer correctly raises integrity and consistency errors on
// timeout conditions.
//
//********************************************************************************
#include <stdint.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile uint32_t rst_cnt = 0;

void main(void) {

    // Improve coverage, toggle lifecycle state and counter after escalation
    if (rst_cnt == 1) {
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
        while(1);
    }

    rst_cnt = 1;
    VPRINTF(LOW, "=================\nLCC check timeout\n=================\n\n");

    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    lcc_initialization();
    grant_mcu_for_fc_writes();

    transition_state_check(TEST_UNLOCKED0, raw_unlock_token);

    uint32_t status;

    // Step 1: Check OTP controller initialization status
    VPRINTF(LOW, "DEBUG: Checking OTP controller initialization status...\n");
    status = lsu_read_32(SOC_OTP_CTRL_STATUS);
    // Check for error bits in the status register
    if (status & (OTP_CTRL_STATUS_DAI_IDLE_MASK - 1) != 0 ) { // Mask all bits except DAI_IDLE
        VPRINTF(LOW, "ERROR: OTP controller initialization failed. STATUS: 0x%08X\n", status);
        return;
    }
    wait_dai_op_idle(0);
    VPRINTF(LOW, "INFO: OTP controller successfully initialized. STATUS: 0x%08X\n", status);
    // Step 2: Set up periodic background checks
    VPRINTF(LOW, "DEBUG: Configuring periodic background checks...\n");

    // Configure CHECK_TIMEOUT
    uint32_t check_timeout = 0x1; // Example value, adjust as needed
    lsu_write_32(SOC_OTP_CTRL_CHECK_TIMEOUT, check_timeout);
    VPRINTF(LOW, "INFO: CHECK_TIMEOUT set to 0x%08X\n", check_timeout);
    // Configure INTEGRITY_CHECK_PERIOD
    uint32_t integrity_check_period = 0; // Example value, adjust as needed
    lsu_write_32(SOC_OTP_CTRL_INTEGRITY_CHECK_PERIOD, integrity_check_period);
    VPRINTF(LOW, "INFO: INTEGRITY_CHECK_PERIOD set to 0x%08X\n", integrity_check_period);
    // Configure CONSISTENCY_CHECK_PERIOD
    uint32_t consistency_check_period = 0; // Example value, adjust as needed
    lsu_write_32(SOC_OTP_CTRL_CONSISTENCY_CHECK_PERIOD, consistency_check_period);
    VPRINTF(LOW, "INFO: CONSISTENCY_CHECK_PERIOD set to 0x%08X\n", consistency_check_period);
    // Step 3: Lock down background check registers
    VPRINTF(LOW, "DEBUG: Locking background check registers...\n");
    lsu_write_32(SOC_OTP_CTRL_CHECK_REGWEN, 0x0);
    VPRINTF(LOW, "INFO: CHECK_REGWEN locked.\n");
    // Step 4: Wait for lfsr to finish
    do {
        status = lsu_read_32(SOC_OTP_CTRL_STATUS);
        for (uint16_t ii = 0; ii < 160; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    } while (status & OTP_CTRL_STATUS_CHECK_PENDING_MASK);

    // Randomly choose between integrity and consistency check triggers.
    uint32_t rand_val = xorshift32();
    uint32_t mask_val;
    const char *path_name;
    if (rand_val & 1) {
        lsu_write_32(SOC_OTP_CTRL_CHECK_TRIGGER, OTP_CTRL_CHECK_TRIGGER_INTEGRITY_MASK);
    } else {
        lsu_write_32(SOC_OTP_CTRL_CHECK_TRIGGER, OTP_CTRL_CHECK_TRIGGER_CONSISTENCY_MASK);
    }

    status = lsu_read_32(SOC_MCI_TOP_MCI_REG_AGG_ERROR_FATAL);

    if (!(status & MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL19_MASK)) {
        VPRINTF(LOW, "ERROR: Expected fatal error to be raised, but got %08x\n", status);
        SEND_STDOUT_CTRL(0x01);
    }
    // Wait for the propagation
    for (uint16_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
    while(1);
}
