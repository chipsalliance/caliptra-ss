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
    initialize_otp_controller();
}

static void expect_reg(uint32_t addr, uint32_t expected, const char *msg) {
    uint32_t actual = lsu_read_32(addr);
    if (actual != expected) {
        handle_error("ERROR: %s expected 0x%08x actual 0x%08x\n", msg, expected, actual);
    }
}

static void expect_dai_wr(uint32_t addr, uint32_t data, uint32_t granularity,
                          uint32_t exp_status, const char *msg) {
    // wdata1 pinned to all-ones to preserve OTP write-once semantics if any
    // address is re-programmed (OTP RAM persists across FC controller reset).
    if (!dai_wr(addr, data, 0xFFFFFFFFu, granularity, exp_status)) {
        handle_error("ERROR: %s\n", msg);
    }
}

static void test_reset_clears_locks(void) {
    lsu_write_32(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, 1u << 0);
    lsu_write_32(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, 1u << 0);
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 1u << 0);

    expect_reg(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, 1u << 0, "PROD PK lock not set before reset");
    expect_reg(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, 1u << 0, "MANUF PK lock not set before reset");
    expect_reg(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 1u << 0, "ratchet lock not set before reset");

    reset_fc_for_next_case();

    expect_reg(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, 0, "PROD PK lock did not clear on reset");
    expect_reg(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, 0, "MANUF PK lock did not clear on reset");
    expect_reg(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0, "ratchet lock did not clear on reset");

    expect_dai_wr(CPTRA_CORE_VENDOR_PK_HASH_1, 0x56000001, 32, 0,
                  "PROD vendor PK hash 1 remained locked after reset");
    expect_dai_wr(CPTRA_CORE_VENDOR_PK_HASH_0, 0x56000000, 32, 0,
                  "MANUF vendor PK hash 0 remained locked after reset");
    expect_dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_0].address, 0x56000010,
                  partitions[CPTRA_SS_LOCK_HEK_PROD_0].granularity, 0,
                  "ratchet seed partition 0 remained locked after reset");
}

void main(void) {
    init_test();
    test_reset_clears_locks();
    SEND_STDOUT_CTRL(0xff);
}
