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

static void test_prod_independence(void) {
    // Lock PROD bit 0 -> locks CPTRA_CORE_VENDOR_PK_HASH_1 (the marker entry).
    // Disjoint blank entries are used in every sub-case so no OTP word is
    // re-programmed across sub-cases (OTP RAM persists across the FC reset).
    if (!dai_lock_blocks_write(CPTRA_CORE_VENDOR_PK_HASH_1, 32,
                               SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, 1u << 0)) {
        handle_error("ERROR: locked PROD vendor PK hash 1 was modified despite the volatile lock\n");
    }
    // Register independence: the PROD lock must not set the other lock CSRs.
    expect_reg(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, 0, "PROD lock changed MANUF lock register");
    expect_reg(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0, "PROD lock changed ratchet lock register");
    // Write independence: other unlocked entries remain writable.
    if (!dai_wr(CPTRA_CORE_VENDOR_PK_HASH_2, 0x11111111u, 0, 32, 0)) {
        handle_error("ERROR: unlocked PROD vendor PK hash 2 was affected by PROD lock\n");
    }
    if (!dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_0].address, 0x11111111u, 0x11111111u,
                partitions[CPTRA_SS_LOCK_HEK_PROD_0].granularity, 0)) {
        handle_error("ERROR: ratchet seed partition 0 was affected by PROD lock\n");
    }
}

static void test_manuf_independence(void) {
    // Lock MANUF bit 0 -> locks CPTRA_CORE_VENDOR_PK_HASH_0 (the marker entry).
    reset_fc_for_next_case();
    if (!dai_lock_blocks_write(CPTRA_CORE_VENDOR_PK_HASH_0, 32,
                               SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, 1u << 0)) {
        handle_error("ERROR: locked MANUF vendor PK hash 0 was modified despite the volatile lock\n");
    }
    expect_reg(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, 0, "MANUF lock changed PROD lock register");
    expect_reg(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0, "MANUF lock changed ratchet lock register");
    if (!dai_wr(CPTRA_CORE_VENDOR_PK_HASH_3, 0x22222222u, 0, 32, 0)) {
        handle_error("ERROR: unlocked PROD vendor PK hash 3 was affected by MANUF lock\n");
    }
    if (!dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_1].address, 0x22222222u, 0x22222222u,
                partitions[CPTRA_SS_LOCK_HEK_PROD_1].granularity, 0)) {
        handle_error("ERROR: ratchet seed partition 1 was affected by MANUF lock\n");
    }
}

static void test_ratchet_independence(void) {
    // Lock ratchet bit 2 -> locks HekProd_2 (the marker entry). Bits 0/1 select
    // HekProd_0/1, which are written as unselected entries above, so bit 2 keeps
    // the locked entry disjoint and blank.
    reset_fc_for_next_case();
    if (!dai_lock_blocks_write(partitions[CPTRA_SS_LOCK_HEK_PROD_2].address,
                               partitions[CPTRA_SS_LOCK_HEK_PROD_2].granularity,
                               SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 1u << 2)) {
        handle_error("ERROR: locked ratchet seed partition 2 was modified despite the volatile lock\n");
    }
    expect_reg(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, 0, "ratchet lock changed PROD lock register");
    expect_reg(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, 0, "ratchet lock changed MANUF lock register");
    if (!dai_wr(CPTRA_CORE_VENDOR_PK_HASH_4, 0x44444444u, 0, 32, 0)) {
        handle_error("ERROR: unlocked PROD vendor PK hash 4 was affected by ratchet lock\n");
    }
    if (!dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_3].address, 0x44444444u, 0x44444444u,
                partitions[CPTRA_SS_LOCK_HEK_PROD_3].granularity, 0)) {
        handle_error("ERROR: unselected ratchet seed partition 3 was affected by ratchet lock\n");
    }
}

void main(void) {
    init_test();
    test_prod_independence();
    test_manuf_independence();
    test_ratchet_independence();
    SEND_STDOUT_CTRL(0xff);
}
