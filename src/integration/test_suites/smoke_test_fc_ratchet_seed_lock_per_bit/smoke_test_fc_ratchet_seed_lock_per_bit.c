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
#include <stdint.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"
#include "fuse_ctrl_mmap.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

static void init_test(void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
    lcc_initialization();
    grant_mcu_for_fc_writes();
    initialize_otp_controller();
}

static void reset_fc_for_next_case(void) {
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);
    grant_mcu_for_fc_writes();
}

static void expect_reg(uint32_t addr, uint32_t expected, const char *msg) {
    uint32_t actual = lsu_read_32(addr);
    if (actual != expected) {
        handle_error("ERROR: %s expected 0x%08x actual 0x%08x\n", msg, expected, actual);
    }
}

static void test_ratchet_bit0_lock(void) {
    // Prove ratchet bit 0 blocks writes to HEK_PROD_0 (the marker entry).
    if (!dai_lock_blocks_write(partitions[CPTRA_SS_LOCK_HEK_PROD_0].address,
                               partitions[CPTRA_SS_LOCK_HEK_PROD_0].granularity,
                               SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 1u << 0)) {
        handle_error("ERROR: locked ratchet seed partition 0 was modified despite the volatile lock\n");
    }
    expect_reg(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 1u << 0, "ratchet lock bit 0 not set");
    // Unselected partition (HEK_PROD_4, disjoint blank) remains writable.
    if (!dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_4].address, 0x54000001, 0x54000001,
                partitions[CPTRA_SS_LOCK_HEK_PROD_4].granularity, 0)) {
        handle_error("ERROR: unselected ratchet seed partition 4 was unexpectedly locked\n");
    }
}

static void test_ratchet_bit1_accumulation_lock(void) {
    reset_fc_for_next_case();
    // Stickiness on bit 0: set it, write 0, confirm it is still set.
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 1u << 0);
    expect_reg(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 1u << 0, "ratchet lock bit 0 not set");
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0);
    expect_reg(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 1u << 0,
               "writing 0 cleared sticky ratchet seed lock bit 0");
    // Prove bit 1 blocks writes to HEK_PROD_1; the helper also sets bit 1, which
    // must accumulate onto the already-set bit 0.
    if (!dai_lock_blocks_write(partitions[CPTRA_SS_LOCK_HEK_PROD_1].address,
                               partitions[CPTRA_SS_LOCK_HEK_PROD_1].granularity,
                               SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 1u << 1)) {
        handle_error("ERROR: locked ratchet seed partition 1 was modified despite the volatile lock\n");
    }
    expect_reg(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, (1u << 0) | (1u << 1),
               "ratchet lock did not accumulate bits 0 and 1");
    // Unselected partition (HEK_PROD_5, disjoint blank) remains writable.
    if (!dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_5].address, 0x54000022, 0x54000022,
                partitions[CPTRA_SS_LOCK_HEK_PROD_5].granularity, 0)) {
        handle_error("ERROR: unselected ratchet seed partition 5 was unexpectedly locked\n");
    }
}

static void test_ratchet_per_bit(void) {
    test_ratchet_bit0_lock();
    test_ratchet_bit1_accumulation_lock();
}

void main(void) {
    init_test();
    test_ratchet_per_bit();
    SEND_STDOUT_CTRL(0xff);
}
