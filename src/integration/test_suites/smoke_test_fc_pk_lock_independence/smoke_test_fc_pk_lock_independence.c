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
    // wdata1 is pinned to all-ones so that an OTP address re-programmed across
    // sub-cases never has to transition a wdata1 bit from 1 to 0 (which the
    // OTP macro flags as MacroWriteBlankError). OTP RAM persists across the
    // FC controller reset done between sub-cases. Sub-case wdata0 values must
    // be bit-additive on any address that is written in more than one sub-case.
    if (!dai_wr(addr, data, 0xFFFFFFFFu, granularity, exp_status)) {
        handle_error("ERROR: %s\n", msg);
    }
}

static void test_prod_independence(void) {
    // PROD lock bit 0 → locks CPTRA_CORE_VENDOR_PK_HASH_1 only.
    // Success writes: MANUF Hash_0, PROD Hash_2, ratchet HekProd_0 (all virgin).
    lsu_write_32(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, 1u << 0);
    expect_reg(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, 0, "PROD lock changed MANUF lock register");
    expect_reg(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0, "PROD lock changed ratchet lock register");
    expect_dai_wr(CPTRA_CORE_VENDOR_PK_HASH_0, 0x00000001u, 32, 0,
                  "MANUF vendor PK hash 0 was affected by PROD lock");
    expect_dai_wr(CPTRA_CORE_VENDOR_PK_HASH_2, 0x00000020u, 32, 0,
                  "unlocked PROD vendor PK hash 2 was affected by PROD lock bit 0");
    expect_dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_0].address, 0x00000010u,
                  partitions[CPTRA_SS_LOCK_HEK_PROD_0].granularity, 0,
                  "ratchet seed partition 0 was affected by PROD lock");
    expect_dai_wr(CPTRA_CORE_VENDOR_PK_HASH_1, 0x00000001u, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK,
                  "locked PROD vendor PK hash 1 write was not rejected");
}

static void test_manuf_independence(void) {
    // MANUF lock bit 0 → locks CPTRA_CORE_VENDOR_PK_HASH_0 only.
    // Success writes: PROD Hash_3 (virgin), ratchet HekProd_1 (virgin).
    // Skip MANUF success write; the only MANUF slot is the one we are locking.
    reset_fc_for_next_case();
    lsu_write_32(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, 1u << 0);
    expect_reg(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, 0, "MANUF lock changed PROD lock register");
    expect_reg(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0, "MANUF lock changed ratchet lock register");
    expect_dai_wr(CPTRA_CORE_VENDOR_PK_HASH_3, 0x00000040u, 32, 0,
                  "unlocked PROD vendor PK hash 3 was affected by MANUF lock");
    expect_dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_1].address, 0x00000020u,
                  partitions[CPTRA_SS_LOCK_HEK_PROD_1].granularity, 0,
                  "ratchet seed partition 1 was affected by MANUF lock");
    expect_dai_wr(CPTRA_CORE_VENDOR_PK_HASH_0, 0x00000100u, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK,
                  "locked MANUF vendor PK hash 0 write was not rejected");
}

static void test_ratchet_independence(void) {
    // RATCHET lock bit 0 → locks ratchet HekProd_0 only.
    // Success writes: MANUF Hash_0 (REWRITE - bit-additive: 0x1 → 0x3), PROD Hash_4 (virgin).
    // The Hash_0 wdata0 is strictly additive over the prod sub-case so OTP
    // only programs new 0→1 bit transitions (no 1→0 to violate write-once).
    reset_fc_for_next_case();
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 1u << 0);
    expect_reg(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, 0, "ratchet lock changed PROD lock register");
    expect_reg(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, 0, "ratchet lock changed MANUF lock register");
    expect_dai_wr(CPTRA_CORE_VENDOR_PK_HASH_0, 0x00000003u, 32, 0,
                  "MANUF vendor PK hash 0 was affected by ratchet lock");
    expect_dai_wr(CPTRA_CORE_VENDOR_PK_HASH_4, 0x00000080u, 32, 0,
                  "unlocked PROD vendor PK hash 4 was affected by ratchet lock");
    expect_dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_0].address, 0x00000200u,
                  partitions[CPTRA_SS_LOCK_HEK_PROD_0].granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK,
                  "locked ratchet seed partition 0 write was not rejected");
}

void main(void) {
    init_test();
    test_prod_independence();
    test_manuf_independence();
    test_ratchet_independence();
    SEND_STDOUT_CTRL(0xff);
}
