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

static void expect_dai_wr(uint32_t addr, uint32_t data, uint32_t granularity,
                          uint32_t exp_status, const char *msg) {
    // wdata1 pinned to all-ones to preserve OTP write-once semantics if any
    // address is re-programmed across sub-cases (the controller is reset
    // between sub-cases but OTP RAM persists).
    if (!dai_wr(addr, data, 0xFFFFFFFFu, granularity, exp_status)) {
        handle_error("ERROR: %s\n", msg);
    }
}

static void expect_manuf_unselected_targets(void) {
    expect_dai_wr(CPTRA_CORE_VENDOR_PK_HASH_1, 0x53000011, 32, 0,
                  "PROD vendor PK hash 1 was affected by MANUF lock");
    expect_dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_0].address, 0x53000022,
                  partitions[CPTRA_SS_LOCK_HEK_PROD_0].granularity, 0,
                  "ratchet seed partition 0 was affected by MANUF lock");
}

static void test_manuf_hash0_lock(void) {
    lsu_write_32(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, 1u);
    expect_reg(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, 1u, "MANUF PK lock bit 0 not set");
    expect_manuf_unselected_targets();
    expect_dai_wr(CPTRA_CORE_VENDOR_PK_HASH_0, 0x53000000, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK,
                  "locked MANUF vendor PK hash 0 write was not rejected");
}

static void test_manuf_pqc0_lock(void) {
    reset_fc_for_next_case();
    lsu_write_32(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, 1u);
    expect_reg(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, 1u, "MANUF PK lock bit 0 not set");
    expect_manuf_unselected_targets();
    expect_dai_wr(CPTRA_CORE_PQC_KEY_TYPE_0, 0x53000001, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK,
                  "locked MANUF vendor PQC key type 0 write was not rejected");
}

void main(void) {
    init_test();
    test_manuf_hash0_lock();
    test_manuf_pqc0_lock();
    SEND_STDOUT_CTRL(0xff);
}
