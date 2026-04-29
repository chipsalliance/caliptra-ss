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
#include <stddef.h>

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

/**
 * Hashed token values. Can be calculated with the following script:
 *   from Crypto.Hash import cSHAKE128
 *   value = 0x0
 *   data = value.to_bytes(16, byteorder='little')
 *   custom = 'LC_CTRL'.encode('UTF-8')
 *   shake = cSHAKE128.new(data=data, custom=custom)
 *   digest = int.from_bytes(shake.read(16), byteorder='little')
 *   print(hex(digest))
 */
static uint32_t hashed_tokens[8][4] = {
    { 0x6db9058d, 0xd5c1d25f, 0xaecf5ff1, 0x3852305b }, // value = 0
    { 0xe65e577c, 0x542f2d2d, 0x73f29e7b, 0xee4fe51a }, // value = 1
    { 0x776a6ed3, 0xac7f4d2a, 0x31bafcef, 0x365671d1 }, // value = 2
    { 0xdcbc2b7f, 0x0f86ccda, 0xa66340c7, 0x56228106 }, // value = 3
    { 0x5ad76df9, 0x8756e714, 0x04f2f7fc, 0x97045d52 }, // value = 4
    { 0x83fedf4e, 0xab931943, 0xeaa495ce, 0x1af9ead2 }, // value = 5
    { 0xe2ad2527, 0x5d416692, 0xe0d874a3, 0xf0113a15 }, // value = 6
    { 0x536a2f30, 0xf47b04d1, 0x2cf01443, 0xf0113a15 }  // value = 7
};

// Perform num_writes 64-bit writes to fuses, starting at tgt_addr. The values to
// be written are from src32, an array of 4*num_writes 32-bit words.
//
// Returns true on success, or stops early and returns false on failure.
bool dai_write_fuses(uint32_t        tgt_addr,
                     const uint32_t *src32,
                     unsigned        num_writes)
{
    for (unsigned i = 0; i < num_writes; i++) {
        if (!dai_wr(tgt_addr + 8 * i, src32[2 * i], src32[2 * i + 1], 64, 0))
            return false;
    }
    return true;
}

// Write hashed_tokens into fuses, starting at base_addr, lock the partition by
// computing a digest, then inject a reset
bool write_tokens(uint32_t base_addr)
{
    // Write the tokens into the partition. These 8 tokens each take two 64-bit
    // writes.
    if (!dai_write_fuses(base_addr, hashed_tokens, 16)) return false;
    if (!calculate_digest(base_addr, 0)) return false;

    reset_fc_lcc_rtl();
    return wait_dai_op_idle(0);
}

/**
 * This function steps through all the test unlock/lock states starting
 * from TEST_UNLOCKED0. Before that all unlock tokens are written into
 * their corresponding fuses in the SECRET_LC_TRANSITION_PARTITION
 * partition which is then locked by computing the hardware digest.
 * Note this is a routine with a long running time.
 */
bool iterate_test_unlock_states(void) {
    if (!transition_state_check(TEST_UNLOCKED0, raw_unlock_token)) return false;

    wait_dai_op_idle(0);

    if (!write_tokens(CPTRA_SS_TEST_UNLOCK_TOKEN_1)) return false;

    for (unsigned tgt_state = TEST_LOCKED0; state <= TEST_UNLOCKED2; state++) {
        VPRINTF(LOW, "LC_CTRL: transition to %d state\n", tgt_state);

        // The lifecycle states are TEST_UNLOCKED0, TEST_LOCKED0, ... and we
        // want to iterate through (some of) them in order. Divide by two to get
        // a "level" value (0 in the two states above).
        unsigned tgt_level = (tgt_state - TEST_LOCKED0) / 2;

        // Is the target lifecycle state unlocked?
        bool tgt_is_unlocked = (tgt_state - TEST_LOCKED0) & 1;

        // We have set up the fuses with hashed versions of rather trivial
        // tokens: TEST_UNLOCKED<n> has token {n, 0, 0, 0}. Form that unhashed
        // token here.
        const uint32_t token[4] = { tgt_level, 0, 0, 0 };

        // We actually only need to pass a token if the tgt_state is unlocked.
        // If not, set token_ptr to NULL.
        const uint32_t *token_ptr = tgt_is_unlocked ? token : NULL;

        // Now perform the transition
        if (!transition_state_check(tgt_state, token_ptr)) return false;
    }
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    lcc_initialization();
    grant_mcu_for_fc_writes();

    bool test_passed = iterate_test_unlock_states();
    if (test_passed) {
        VPRINTF(LOW, "INFO: Smoke Test FC Unlock Transitions Passed!\n");
    } else {
        handle_error("ERROR: Smoke Test FC Unlock Transitions Failed!\n");
    }

    mcu_sleep(160);

    SEND_STDOUT_CTRL(0xFF);
}
