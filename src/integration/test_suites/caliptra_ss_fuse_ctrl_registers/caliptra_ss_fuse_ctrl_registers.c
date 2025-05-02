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
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>

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

#define NUM_READ_LOCK_REGS 7
static uint32_t read_lock_registers[NUM_READ_LOCK_REGS] = {
    SOC_OTP_CTRL_SW_MANUF_PARTITION_READ_LOCK,
    SOC_OTP_CTRL_SVN_PARTITION_READ_LOCK,
    SOC_OTP_CTRL_VENDOR_TEST_PARTITION_READ_LOCK,
    SOC_OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_READ_LOCK,
    SOC_OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_READ_LOCK,
    SOC_OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK,
    SOC_OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK
};

#define NUM_INTER_REGS 3
static uint32_t interrupt_registers[NUM_INTER_REGS] = {
    SOC_OTP_CTRL_INTERRUPT_STATE,
    SOC_OTP_CTRL_INTERRUPT_ENABLE,
    SOC_OTP_CTRL_INTERRUPT_TEST
};

#define NUM_DAI_REGS 4
static uint32_t dai_registers[NUM_DAI_REGS] = {
    SOC_OTP_CTRL_DIRECT_ACCESS_CMD,
    SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS,
    SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_0,
    SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_1
};

#define NUM_REGWEN_REGS 2
static uint32_t regwen_registers[NUM_REGWEN_REGS] = {
    SOC_OTP_CTRL_DIRECT_ACCESS_REGWEN,
    SOC_OTP_CTRL_CHECK_TRIGGER_REGWEN,
};

#define NUM_CHECK_REGS 3
static uint32_t check_registers[NUM_CHECK_REGS] = {
    SOC_OTP_CTRL_CHECK_TIMEOUT,
    SOC_OTP_CTRL_INTEGRITY_CHECK_PERIOD,
    SOC_OTP_CTRL_CONSISTENCY_CHECK_PERIOD
};

#define NUM_DIGEST_REGS 28
static uint32_t digest_registers[NUM_DIGEST_REGS] = {
    SOC_OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_DIGEST_0,
    SOC_OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_DIGEST_1,
    SOC_OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_0,
    SOC_OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_1,
    SOC_OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_0,
    SOC_OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_1,
    SOC_OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_DIGEST_0,
    SOC_OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_DIGEST_1,
    SOC_OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_DIGEST_0,
    SOC_OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_DIGEST_1,
    SOC_OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_DIGEST_0,
    SOC_OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_DIGEST_1,
    SOC_OTP_CTRL_SW_MANUF_PARTITION_DIGEST_DIGEST_0,
    SOC_OTP_CTRL_SW_MANUF_PARTITION_DIGEST_DIGEST_1,
    SOC_OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_DIGEST_0,
    SOC_OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_DIGEST_1,
    SOC_OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_DIGEST_0,
    SOC_OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_DIGEST_1,
    SOC_OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_DIGEST_0,
    SOC_OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_DIGEST_1,
    SOC_OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_DIGEST_0,
    SOC_OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_DIGEST_1,
    SOC_OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_DIGEST_0,
    SOC_OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_DIGEST_1,
    SOC_OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_0,
    SOC_OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_1,
    SOC_OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_DIGEST_0,
    SOC_OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_DIGEST_1
};

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    //transition_state_check(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);

    initialize_otp_controller();

    uint32_t value = 0;

    // Make sure all the read lock registers are set to 1 (disabled).
    for (uint32_t i = 0; i < NUM_READ_LOCK_REGS; i++) {
        value = lsu_read_32(read_lock_registers[i]);
        if ((value & 0x1) != 0x1) {
            VPRINTF(LOW, "ERROR: incorrect value in read lock register %08X: exp: %08X act: %08X\n", read_lock_registers[i], 0x1, value);
            goto epilogue;
        }
    }

    // Make sure all the interrupt registers are readable.
    for (uint32_t i = 0; i < NUM_INTER_REGS; i++) {
        value = lsu_read_32(interrupt_registers[i]);
        if (value != 0x0) {
            VPRINTF(LOW, "ERROR: non-zero value in interrupt register %08X: exp: 0 act: %08X\n", interrupt_registers[i], value);
            goto epilogue;
        }
    }

    // Make sure all the DAI registers are readable.
    for (uint32_t i = 0; i < NUM_DAI_REGS; i++) {
        value = lsu_read_32(dai_registers[i]);
        if (value != 0x0) {
            VPRINTF(LOW, "ERROR: incorrect value in dai register %08X: exp: 0 act: %08X\n", interrupt_registers[i], value);
            goto epilogue;
        }
    }

    // Make sure all the regwen registers are set to 1 (enabled).
    for (uint32_t i = 0; i < NUM_REGWEN_REGS; i++) {
        value = lsu_read_32(regwen_registers[i]);
        if ((value & 0x1) != 0x1) {
            VPRINTF(LOW, "ERROR: incorrect value in regwen register %08X: exp: %08X act: %08X\n", regwen_registers[i], 0x1, value);
            goto epilogue;
        }
    }

    // Make sure all the check registers are initialized.
    value = lsu_read_32(SOC_OTP_CTRL_CHECK_REGWEN);
    if (value != 0) {
        VPRINTF(LOW, "ERROR: check registers are not locked\n");
        goto epilogue;
    }
    value = lsu_read_32(SOC_OTP_CTRL_CHECK_TRIGGER);
    if (value != 0) {
        VPRINTF(LOW, "ERROR: check trigger register is not zero\n");
        goto epilogue;
    }
    for (uint32_t i = 0; i < NUM_CHECK_REGS; i++) {
        value = lsu_read_32(check_registers[i]);
        if (value == 0x0) {
            VPRINTF(LOW, "ERROR: zero value in check register %08X\n", check_registers[i]);
            goto epilogue;
        }
    }

    // Make sure all the digest regs are 0.
    for (uint32_t i = 0; i < NUM_DIGEST_REGS; i++) {
        value = lsu_read_32(digest_registers[i]);
        if (value != 0x0) {
            VPRINTF(LOW, "ERROR: non-zero value in digest register %08X\n", digest_registers[i]);
            goto epilogue;
        }
    }

    // Misc. writes
    lsu_write_32(SOC_OTP_CTRL_ALERT_TEST, 0x1);
    lsu_write_32(SOC_OTP_CTRL_CHECK_TRIGGER, 0x1);
    lsu_write_32(SOC_OTP_CTRL_CHECK_TRIGGER_REGWEN, 0x0);
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_REGWEN, 0x0);

epilogue:
    for (uint8_t i = 0; i < 160; i++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
