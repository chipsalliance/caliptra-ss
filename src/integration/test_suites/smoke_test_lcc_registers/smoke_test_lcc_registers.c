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
//
// ## LCC Register Test
// 
// This test reads and writes all registers in the LCC.
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"

#define MUBITRUE 0x96
#define MUBIFALSE 0x69

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// This function writes to a read-only register and checks whether the expected
// reset value is still present after the write.
void check_read_only_register(uintptr_t addr, uint32_t expected_value, uint32_t mask) {
    // Perform the write.
    lsu_write_32(addr, 0xdeadbeef);

    // Wait a bit before reading out the value.
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    uint32_t value = lsu_read_32(addr) & mask;

    if (expected_value != value) {
        VPRINTF(LOW, "ERROR: incorrect value: exp: %d, act: %d\n", expected_value, value);
        exit(1);
    }
}

void test_read_only_registers(void) {
    VPRINTF(LOW, "============\nMCU: TESTING RO LCC REGISTERS\n============\n\n");

    // STATUS register.
    // Read-only 32-bit register.
    uint32_t status = lsu_read_32(LC_CTRL_STATUS_OFFSET);
    check_read_only_register(LC_CTRL_STATUS_OFFSET, status, 0xFFFFFFFF);

    // TRANSITION_REGWEN register.
    // Read-only 1-bit register.
    uint32_t transition_regwen = lsu_read_32(LC_CTRL_TRANSITION_REGWEN_OFFSET) & 0x1;
    check_read_only_register(LC_CTRL_TRANSITION_REGWEN_OFFSET, transition_regwen, 0x1);

    // OTP_VENDOR_TEST_STATUS register.
    // Read-only 32-bit register.
    uint32_t otp_vendor_test_status = lsu_read_32(LC_CTRL_OTP_VENDOR_TEST_STATUS_OFFSET);
    check_read_only_register(LC_CTRL_OTP_VENDOR_TEST_STATUS_OFFSET, otp_vendor_test_status, 0xFFFFFFFF);

    // LC_STATE register.
    // Read-only 30-bit register.
    uint32_t lc_state = lsu_read_32(LC_CTRL_LC_STATE_OFFSET) & 0x3FFFFFFF;
    check_read_only_register(LC_CTRL_LC_STATE_OFFSET, lc_state, 0x3FFFFFFF);

    // LC_TRANSITION_CNT register.
    // Read-only 5-bit register.
    uint32_t lc_transition_cnt = lsu_read_32(LC_CTRL_LC_TRANSITION_CNT_OFFSET) & 0x1F;
    check_read_only_register(LC_CTRL_LC_TRANSITION_CNT_OFFSET, lc_transition_cnt, 0x1F);

    // LC_ID_STATE register.
    // Read-only 32-bit register.
    uint32_t lc_id_state = lsu_read_32(LC_CTRL_LC_ID_STATE_OFFSET);
    check_read_only_register(LC_CTRL_LC_ID_STATE_OFFSET, lc_id_state, 0xFFFFFFFF);

    // LC_CTRL_HW_REVISION0 register.
    // Read-only 32-bit register.
    // SILICON_CREATOR_ID and the PRODUCT_ID.
    uint32_t hw_revision0 = lsu_read_32(LC_CTRL_HW_REVISION0_OFFSET);
    check_read_only_register(LC_CTRL_HW_REVISION0_OFFSET, hw_revision0, 0xFFFFFFFF);

    // LC_CTRL_HW_REVISION1 register.
    // Read-only 32-bit register.
    // PRODUCT_REVISION_ID and the RESERVED.
    uint32_t hw_revision1 = lsu_read_32(LC_CTRL_HW_REVISION1_OFFSET);
    check_read_only_register(LC_CTRL_HW_REVISION1_OFFSET, hw_revision1, 0xFFFFFFFF);

    // LC_CTRL_DEVICE_ID register.
    // Read-only 256-bit register.
    uint32_t device_id = lsu_read_32(LC_CTRL_DEVICE_ID_0_OFFSET);
    check_read_only_register(LC_CTRL_DEVICE_ID_0_OFFSET, device_id, 0xFFFFFFFF);
    device_id = lsu_read_32(LC_CTRL_DEVICE_ID_1_OFFSET);
    check_read_only_register(LC_CTRL_DEVICE_ID_1_OFFSET, device_id, 0xFFFFFFFF);
    device_id = lsu_read_32(LC_CTRL_DEVICE_ID_2_OFFSET);
    check_read_only_register(LC_CTRL_DEVICE_ID_2_OFFSET, device_id, 0xFFFFFFFF);
    device_id = lsu_read_32(LC_CTRL_DEVICE_ID_3_OFFSET);
    check_read_only_register(LC_CTRL_DEVICE_ID_3_OFFSET, device_id, 0xFFFFFFFF);
    device_id = lsu_read_32(LC_CTRL_DEVICE_ID_4_OFFSET);
    check_read_only_register(LC_CTRL_DEVICE_ID_4_OFFSET, device_id, 0xFFFFFFFF);
    device_id = lsu_read_32(LC_CTRL_DEVICE_ID_5_OFFSET);
    check_read_only_register(LC_CTRL_DEVICE_ID_5_OFFSET, device_id, 0xFFFFFFFF);
    device_id = lsu_read_32(LC_CTRL_DEVICE_ID_6_OFFSET);
    check_read_only_register(LC_CTRL_DEVICE_ID_6_OFFSET, device_id, 0xFFFFFFFF);
    device_id = lsu_read_32(LC_CTRL_DEVICE_ID_7_OFFSET);
    check_read_only_register(LC_CTRL_DEVICE_ID_7_OFFSET, device_id, 0xFFFFFFFF);

    // LC_CTRL_MANUF_STATE register.
    // Read-only 256-bit register.
    uint32_t manuf_state = lsu_read_32(LC_CTRL_MANUF_STATE_0_OFFSET);
    check_read_only_register(LC_CTRL_MANUF_STATE_0_OFFSET, manuf_state, 0xFFFFFFFF);
    manuf_state = lsu_read_32(LC_CTRL_MANUF_STATE_1_OFFSET);
    check_read_only_register(LC_CTRL_MANUF_STATE_1_OFFSET, manuf_state, 0xFFFFFFFF);
    manuf_state = lsu_read_32(LC_CTRL_MANUF_STATE_2_OFFSET);
    check_read_only_register(LC_CTRL_MANUF_STATE_2_OFFSET, manuf_state, 0xFFFFFFFF);
    manuf_state = lsu_read_32(LC_CTRL_MANUF_STATE_3_OFFSET);
    check_read_only_register(LC_CTRL_MANUF_STATE_3_OFFSET, manuf_state, 0xFFFFFFFF);
    manuf_state = lsu_read_32(LC_CTRL_MANUF_STATE_4_OFFSET);
    check_read_only_register(LC_CTRL_MANUF_STATE_4_OFFSET, manuf_state, 0xFFFFFFFF);
    manuf_state = lsu_read_32(LC_CTRL_MANUF_STATE_5_OFFSET);
    check_read_only_register(LC_CTRL_MANUF_STATE_5_OFFSET, manuf_state, 0xFFFFFFFF);
    manuf_state = lsu_read_32(LC_CTRL_MANUF_STATE_6_OFFSET);
    check_read_only_register(LC_CTRL_MANUF_STATE_6_OFFSET, manuf_state, 0xFFFFFFFF);
    manuf_state = lsu_read_32(LC_CTRL_MANUF_STATE_7_OFFSET);
    check_read_only_register(LC_CTRL_MANUF_STATE_7_OFFSET, manuf_state, 0xFFFFFFFF);

    VPRINTF(LOW, "============\nMCU: TESTING RO LCC REGISTERS FINISHED\n============\n\n");
}

void test_write_only_registers(void) {
    VPRINTF(LOW, "============\nMCU: TESTING WO LCC REGISTERS\n============\n\n");

    // ALERT_TEST_OFFSET register.
    // Write-only 3-bit register.
    // First try to read from the register.
    uint32_t reg_value = lsu_read_32(LC_CTRL_ALERT_TEST_OFFSET) & 0x7;
    // Now write a value into the register.
    uint32_t reg_write_value = (~reg_value) & 0x7;
    lsu_write_32(LC_CTRL_ALERT_TEST_OFFSET, reg_write_value);
    // Wait a bit before reading out the value.
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    // Read out value.
    reg_value = lsu_read_32(LC_CTRL_ALERT_TEST_OFFSET) & 0x7;
    // Value should not be reg_write_value.
    if (reg_value == reg_write_value) {
        VPRINTF(LOW, "ERROR: read from write only register worked\n");
        exit(1);
    }

    VPRINTF(LOW, "============\nMCU: TESTING WO LCC REGISTERS FINISHED\n============\n\n");
}

void test_transition_cmd_ctrl_registers(void) {
    VPRINTF(LOW, "============\nMCU: TESTING TRANSITION LCC REGISTERS\n============\n\n");

    // TRANSITION_CMD register.
    // r0w1c 1-bit register.
    // Check if we get a 0 back if we read.
    uint32_t transition_cmd = lsu_read_32(LC_CTRL_TRANSITION_CMD_OFFSET) & 0x01;
    if (transition_cmd != 0) {
        VPRINTF(LOW, "ERROR: incorrect transition_cmd: exp: %d, act: %d\n", 0, transition_cmd);
        exit(1);
    }

    // Now write a 1 into the register.
    lsu_write_32(LC_CTRL_TRANSITION_CMD_OFFSET, 0x0);

    // Read back value, should still be 0.
    transition_cmd = lsu_read_32(LC_CTRL_TRANSITION_CMD_OFFSET) & 0x01;
    if (transition_cmd != 0) {
        VPRINTF(LOW, "ERROR: incorrect transition_cmd: exp: %d, act: %d\n", 0, transition_cmd);
        exit(1);
    }

    // TRANSITION_CTRL register.
    // 2-bit register.
    // Check if we get a 0 back if we read.
    uint32_t transition_ctrl = lsu_read_32(LC_CTRL_TRANSITION_CTRL_OFFSET) & 0x03;
    if (transition_ctrl != 0) {
        VPRINTF(LOW, "ERROR: incorrect transition_ctrl: exp: %d, act: %d\n", 0, transition_ctrl);
        exit(1);
    }

    VPRINTF(LOW, "============\nMCU: TESTING TRANSITION LCC REGISTERS FINISHED\n============\n\n");
}

void check_transition_tokens(uint32_t transition_token0, uint32_t transition_token1, uint32_t transition_token2,
                             uint32_t transition_token3, uint32_t transition_token0_exp, uint32_t transition_token1_exp,
                             uint32_t transition_token2_exp, uint32_t transition_token3_exp) {
    if (transition_token0 != transition_token0_exp) {
        VPRINTF(LOW, "ERROR: incorrect transition_token0: exp: %d, act: %d\n", transition_token0_exp, transition_token0);
        exit(1);
    }
    if (transition_token1 != transition_token1_exp) {
        VPRINTF(LOW, "ERROR: incorrect transition_token1: exp: %d, act: %d\n", transition_token1_exp, transition_token1);
        exit(1);
    }
    if (transition_token2 != transition_token2_exp) {
        VPRINTF(LOW, "ERROR: incorrect transition_token2: exp: %d, act: %d\n", transition_token2_exp, transition_token2);
        exit(1);
    }
    if (transition_token3 != transition_token3_exp) {
        VPRINTF(LOW, "ERROR: incorrect transition_token3: exp: %d, act: %d\n", transition_token3_exp, transition_token3);
        exit(1);
    }
}

void test_read_write_registers(int regwen) {
    VPRINTF(LOW, "==========\nMCU: TESTING RW LCC REGISTERS WITH REGWEN=%d\n==========\n\n", regwen);

    // TRANSITION_TOKEN register.
    // Read-write 128-bit register locked / unlocked with TRANSITION_REGWEN.
    // Check if value matches reset value of '0.
    uint32_t transition_token0_exp = 0;
    uint32_t transition_token1_exp = 0;
    uint32_t transition_token2_exp = 0;
    uint32_t transition_token3_exp = 0;
    uint32_t transition_token0 = lsu_read_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET);
    uint32_t transition_token1 = lsu_read_32(LC_CTRL_TRANSITION_TOKEN_1_OFFSET);
    uint32_t transition_token2 = lsu_read_32(LC_CTRL_TRANSITION_TOKEN_2_OFFSET);
    uint32_t transition_token3 = lsu_read_32(LC_CTRL_TRANSITION_TOKEN_3_OFFSET);
    check_transition_tokens(transition_token0, transition_token1, transition_token2, transition_token3,
                            transition_token0_exp, transition_token1_exp, transition_token2_exp, transition_token3_exp);

    // Write to the register and check if the value is correctly stored in the register.
    uint32_t transition_token0_write = 0xB16B00B5;
    uint32_t transition_token1_write = 0xABADBABE;
    uint32_t transition_token2_write = 0x000FF1CE;
    uint32_t transition_token3_write = 0xBAADF00D;
    lsu_write_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET, transition_token0_write);
    lsu_write_32(LC_CTRL_TRANSITION_TOKEN_1_OFFSET, transition_token1_write);
    lsu_write_32(LC_CTRL_TRANSITION_TOKEN_2_OFFSET, transition_token2_write);
    lsu_write_32(LC_CTRL_TRANSITION_TOKEN_3_OFFSET, transition_token3_write);

    // Wait a bit before reading out the value.
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    if (regwen) {
        transition_token0_exp = transition_token0_write;
        transition_token1_exp = transition_token1_write;
        transition_token2_exp = transition_token2_write;
        transition_token3_exp = transition_token3_write;
    }
    transition_token0 = lsu_read_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET);
    transition_token1 = lsu_read_32(LC_CTRL_TRANSITION_TOKEN_1_OFFSET);
    transition_token2 = lsu_read_32(LC_CTRL_TRANSITION_TOKEN_2_OFFSET);
    transition_token3 = lsu_read_32(LC_CTRL_TRANSITION_TOKEN_3_OFFSET);
    check_transition_tokens(transition_token0, transition_token1, transition_token2, transition_token3,
                            transition_token0_exp, transition_token1_exp, transition_token2_exp, transition_token3_exp);
    
    // TRANSITION_TARGET register.
    // Read-write 30-bit register locked / unlocked with TRANSITION_REGWEN.
    // Check if value matches reset value of '0.
    uint32_t transition_target_exp = 0;
    uint32_t transition_target = lsu_read_32(LC_CTRL_TRANSITION_TARGET_OFFSET) & 0x3fffffff;
    if (transition_target != transition_target_exp) {
        VPRINTF(LOW, "ERROR: incorrect transition_target: exp: %d, act: %d\n", transition_target_exp, transition_target);
        exit(1);
    }
    // Write to the register and check if the value is correctly stored in the register.
    uint32_t transition_target_write = 0xE011CFD0 & 0x3fffffff;
    lsu_write_32(LC_CTRL_TRANSITION_TARGET_OFFSET, transition_target_write);
    // Wait a bit before reading out the value.
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    if (regwen) {
        transition_target_exp = transition_target_write;
    } else {
        transition_target_exp = 0;
    }
    transition_target = lsu_read_32(LC_CTRL_TRANSITION_TARGET_OFFSET) & 0x3fffffff;
    if (transition_target != transition_target_exp) {
        VPRINTF(LOW, "ERROR: incorrect transition_target: exp: %u, act: %u\n", transition_target_exp, transition_target);
        exit(1);
    }
    
    // OTP_VENDOR_TEST_CTRL register.
    // Read-write 32-bit register locked / unlocked with TRANSITION_REGWEN.
    // Check if value matches reset value of '0.
    uint32_t otp_vendor_test_ctrl_exp = 0;
    uint32_t otp_vendor_test_ctrl = lsu_read_32(LC_CTRL_OTP_VENDOR_TEST_CTRL_OFFSET);
    if (otp_vendor_test_ctrl != otp_vendor_test_ctrl_exp) {
        VPRINTF(LOW, "ERROR: incorrect otp_vendor_test_ctrl: exp: %u, act: %u\n", otp_vendor_test_ctrl_exp, otp_vendor_test_ctrl);
        exit(1);
    }
    // Write to the register and check if the value is correctly stored in the register.
    uint32_t otp_vendor_test_ctrl_write = 0xcafebabe;
    lsu_write_32(LC_CTRL_OTP_VENDOR_TEST_CTRL_OFFSET, otp_vendor_test_ctrl_write);
    // Wait a bit before reading out the value.
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    if (regwen) {
        otp_vendor_test_ctrl_exp = otp_vendor_test_ctrl_write;
    } else {
        otp_vendor_test_ctrl_exp = 0;
    }
    otp_vendor_test_ctrl = lsu_read_32(LC_CTRL_OTP_VENDOR_TEST_CTRL_OFFSET);
    if (otp_vendor_test_ctrl != otp_vendor_test_ctrl_exp) {
        VPRINTF(LOW, "ERROR: incorrect otp_vendor_test_ctrl: exp: %u, act: %u\n", otp_vendor_test_ctrl_exp, otp_vendor_test_ctrl);
        exit(1);
    }
    VPRINTF(LOW, "==========\nMCU: TESTING RW LCC REGISTERS FINISHED\n==========\n\n", regwen);
}

void test_transition_if(int lock_register) {
    VPRINTF(LOW, "============\nMCU: TESTING TRANSITION_IF LCC REGISTERS\n============\n\n");

    // CLAIM_TRANSITION_IF register.
    // Read-write 8-bit register that can be enabled with CLAIM_TRANSITION_IF_REGWEN.
    lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, MUBIFALSE);
    uint32_t claim_transition_if_exp = MUBIFALSE;
    uint32_t claim_transition_if = lsu_read_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET) & 0xFF;
    if (claim_transition_if != claim_transition_if_exp) {
        VPRINTF(LOW, "ERROR: incorrect claim_transition_if: exp: %d, act: %d\n", claim_transition_if_exp, claim_transition_if);
        exit(1);
    }

    // CLAIM_TRANSITION_IF_REGWEN register.
    // rw0c 1-bit register
    uint32_t claim_transition_if_regwen_exp = 1;
    uint32_t claim_transition_if_regwen = lsu_read_32(LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_OFFSET) & 0x1;
    if (claim_transition_if_regwen != claim_transition_if_regwen_exp) {
        VPRINTF(LOW, "ERROR: incorrect claim_transition_if_regwen: exp: %d, act: %d\n", claim_transition_if_regwen_exp, claim_transition_if_regwen);
        exit(1);
    }

    if (lock_register) {
        // Clear the regwen.
        lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_OFFSET, 0);
        claim_transition_if_regwen_exp = 0;
        claim_transition_if_regwen = lsu_read_32(LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_OFFSET) & 0x1;
        if (claim_transition_if_regwen != claim_transition_if_regwen_exp) {
            VPRINTF(LOW, "ERROR: incorrect claim_transition_if_regwen: exp: %d, act: %d\n", claim_transition_if_regwen_exp, claim_transition_if_regwen);
            exit(1);
        }
    }

    // Write to CLAIM_TRANSITION_IF register.
    lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, MUBITRUE);
    if (lock_register) {
        claim_transition_if_exp = MUBIFALSE;
    } else {
        claim_transition_if_exp = MUBITRUE;
    }
    claim_transition_if = lsu_read_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET) & 0xFF;
    if (claim_transition_if != claim_transition_if_exp) {
        VPRINTF(LOW, "ERROR: incorrect claim_transition_if: exp: %d, act: %d\n", claim_transition_if_exp, claim_transition_if);
        exit(1);
    }

    VPRINTF(LOW, "============\nMCU: TESTING TRANSITION_IF LCC REGISTERS FINISHED\n============\n\n");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU: Caliptra Boot Go\n=================\n\n");    
    mcu_cptra_init_d(.cfg_skip_set_fuse_done=true);
    lcc_initialization();
    VPRINTF(LOW, "==============\nMCU: TESTING LCC REGISTERS\n==============\n\n");

    test_read_only_registers();
    test_write_only_registers();
    test_transition_cmd_ctrl_registers();
    // As REGWEN=0, check if writing is blocked.
    test_read_write_registers(0);
    // This will set the REGWEN=1
    test_transition_if(0);
    // REGWEN now 1, check if writing works.
    test_read_write_registers(1);
    // Check if the REGWEN for the TRANSITION_IF works.
    test_transition_if(1);

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
