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

static const uint32_t prod_hash_addr[15] = {
    CPTRA_CORE_VENDOR_PK_HASH_1, CPTRA_CORE_VENDOR_PK_HASH_2,
    CPTRA_CORE_VENDOR_PK_HASH_3, CPTRA_CORE_VENDOR_PK_HASH_4,
    CPTRA_CORE_VENDOR_PK_HASH_5, CPTRA_CORE_VENDOR_PK_HASH_6,
    CPTRA_CORE_VENDOR_PK_HASH_7, CPTRA_CORE_VENDOR_PK_HASH_8,
    CPTRA_CORE_VENDOR_PK_HASH_9, CPTRA_CORE_VENDOR_PK_HASH_10,
    CPTRA_CORE_VENDOR_PK_HASH_11, CPTRA_CORE_VENDOR_PK_HASH_12,
    CPTRA_CORE_VENDOR_PK_HASH_13, CPTRA_CORE_VENDOR_PK_HASH_14,
    CPTRA_CORE_VENDOR_PK_HASH_15
};

static void test_prod_per_bit(void) {
    // Iterate only over representative bits {0, 7, 14}: low boundary, middle,
    // and high boundary of the 15-bit PROD lock mask. The PQC sub-case was
    // dropped because PQC lives in the same VendorHashesProd partition and
    // is covered by the persistence tests.
    static const uint32_t test_bits[3] = {0u, 7u, 14u};
    // Disjoint unselected targets (never used as a locked marker entry): the
    // markers are prod_hash_addr[{0,7,14}], so HASH_2/3/4 stay virgin.
    static const uint32_t unsel_idx[3] = {1u, 2u, 3u};

    for (uint32_t k = 0; k < 3; k++) {
        const uint32_t i = test_bits[k];

        // Prove lock bit i blocks writes to its hash: program 0x55555555, set
        // bit i, attempt 0xAAAAAAAA, read back 0x55555555.
        if (!dai_lock_blocks_write(prod_hash_addr[i], 32,
                                   SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, 1u << i)) {
            handle_error("ERROR: locked PROD vendor PK hash was modified despite the volatile lock\n");
        }
        expect_reg(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, 1u << i,
                   "PROD PK lock register changed bits other than selected bit");
        // Unselected hash remains writable.
        if (!dai_wr(prod_hash_addr[unsel_idx[k]], 0x52002000u + i, 0, 32, 0)) {
            handle_error("ERROR: unselected PROD vendor PK hash was unexpectedly locked\n");
        }

        if (k + 1 < 3) {
            reset_fc_for_next_case();
        }
    }
}

void main(void) {
    init_test();
    test_prod_per_bit();
    SEND_STDOUT_CTRL(0xff);
}
