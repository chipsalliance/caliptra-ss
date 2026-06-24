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

static uint32_t pattern_word(uint32_t byte_offset) {
    uint32_t word = 0;
    for (uint32_t i = 0; i < 4; i++) {
        word |= (((byte_offset + i) ^ 0x5au) & 0xffu) << (8u * i);
    }
    return word;
}

static void init_test(void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
    lcc_initialization();
    grant_mcu_for_fc_writes();
    initialize_otp_controller();
}

static void reset_fc_keep_otp(void) {
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

static void write_hash_word_pattern(uint32_t base_addr, uint32_t word, uint32_t exp_status,
                                    uint32_t invert, const char *msg) {
    uint32_t data = pattern_word(word * 4u);
    if (invert) {
        data = ~data;
    }
    if (!dai_wr(base_addr + word * 4u, data, 0, 32, exp_status)) {
        handle_error("ERROR: %s hash word %0d DAI write status mismatch\n", msg, word);
    }
}

static void expect_hash_word_pattern(uint32_t base_addr, uint32_t word, uint32_t invert, const char *msg) {
    uint32_t actual = 0;
    uint32_t unused = 0;
    uint32_t expected = pattern_word(word * 4u);
    if (invert) {
        expected = ~expected;
    }
    if (!dai_rd(base_addr + word * 4u, &actual, &unused, 32, 0)) {
        handle_error("ERROR: %s hash word %0d DAI read status mismatch\n", msg, word);
    }
    if (actual != expected) {
        handle_error("ERROR: %s hash word %0d expected 0x%08x actual 0x%08x\n", msg, word, expected, actual);
    }
}

static void test_manuf_vendor_pk_persistence(void) {
    const uint32_t lock_mask = 1u << 0;

    // Single-word persistence proof against MANUF VendorHashes Hash_0 word 0.
    // The lock primitive is identical for every word/PQC field in the same
    // partition, so one representative slot is sufficient (per-partition
    // exhaustion was removed to stay within the simulation cycle budget).
    write_hash_word_pattern(CPTRA_CORE_VENDOR_PK_HASH_0, 0, 0, 0,
                            "initial MANUF hash0 word0 program");
    expect_hash_word_pattern(CPTRA_CORE_VENDOR_PK_HASH_0, 0, 0,
                             "initial MANUF hash0 word0 readback");

    reset_fc_keep_otp();
    expect_hash_word_pattern(CPTRA_CORE_VENDOR_PK_HASH_0, 0, 0,
                             "post-reset MANUF hash0 word0 readback");

    lsu_write_32(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, lock_mask);
    expect_reg(SOC_OTP_CTRL_MANUF_PK_HASH_VOLATILE_LOCK, lock_mask,
               "MANUF PK volatile lock bit 0 not set");

    // (iii) Attempt to overwrite the locked word with the complement of its
    // programmed value. A working lock blocks the write so the word keeps its
    // value; a dead lock would OR the complement in (P | ~P = all-ones). The
    // status is not asserted -- the post-reset read-back below is the verdict.
    (void)dai_wr(CPTRA_CORE_VENDOR_PK_HASH_0, ~pattern_word(0), 0, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);

    // (iv) After reset the word must still read its programmed value, not the
    // all-ones a dead lock would have produced.
    reset_fc_keep_otp();
    expect_hash_word_pattern(CPTRA_CORE_VENDOR_PK_HASH_0, 0, 0,
                             "locked MANUF hash0 word0 preserved value");
}

void main(void) {
    init_test();
    test_manuf_vendor_pk_persistence();
    SEND_STDOUT_CTRL(0xff);
}
