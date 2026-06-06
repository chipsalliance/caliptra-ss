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
    if (!dai_wr(addr, data, data ^ 0xffffffffu, granularity, exp_status)) {
        handle_error("ERROR: %s\n", msg);
    }
}

static void test_sticky_locks(void) {
    const uint32_t prod_mask = 1u << 1;
    const uint32_t manuf_mask = 1u << 0;
    const uint32_t ratchet_mask = 1u << 2;

    lsu_write_32(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, prod_mask);
    lsu_write_32(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, manuf_mask);
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, ratchet_mask);

    lsu_write_32(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, 0);
    lsu_write_32(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, 0);
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0);

    expect_reg(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, prod_mask, "PROD PK lock sticky after write 0");
    expect_reg(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, manuf_mask, "MANUF PK lock sticky after write 0");
    expect_reg(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, ratchet_mask, "ratchet lock sticky after write 0");

    expect_dai_wr(CPTRA_CORE_VENDOR_PK_HASH_2, 0x51000002, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK,
                  "locked PROD vendor PK hash 2 write was not rejected");
    expect_dai_wr(CPTRA_CORE_VENDOR_PK_HASH_0, 0x51000000, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK,
                  "locked MANUF vendor PK hash 0 write was not rejected");
    expect_dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_2].address, 0x51000022,
                  partitions[CPTRA_SS_LOCK_HEK_PROD_2].granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK,
                  "locked ratchet seed partition 2 write was not rejected");
}

void main(void) {
    init_test();
    test_sticky_locks();
    SEND_STDOUT_CTRL(0xff);
}
