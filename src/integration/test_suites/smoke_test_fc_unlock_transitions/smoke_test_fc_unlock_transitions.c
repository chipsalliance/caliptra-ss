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

/**
 * This function steps through all the test unlock/lock states starting
 * from TEST_UNLOCKED0. Before that all unlock tokens are written into
 * their corresponding fuses in the SECRET_LC_TRANSITION_PARTITION
 * partition which is then locked by computing the hardware digest.
 * Note this is a routine with a long running time.
 */
void iterate_test_unlock_states() {

    // 0x4C0: CPTRA_SS_TEST_UNLOCK_TOKEN_0
    const uint32_t base_address = 0x4C0;

    // Write the tokens into the partition.
    for (uint32_t i = 0; i < 3; i++) {
        dai_wr(base_address + 0x10*i, hashed_tokens[i][0], hashed_tokens[i][1], 64, 0);
        dai_wr(base_address + 0x08 + 0x10*i, hashed_tokens[i][2], hashed_tokens[i][3], 64, 0);
    }

    calculate_digest(base_address);

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    for (uint32_t state = TEST_LOCKED0, token = 0x0; state <= TEST_UNLOCKED2; token += (state & 0x1), state++) {
        VPRINTF(LOW, "LC_CTRL: transition to %d state\n", state);

        transition_state(state, token, 0, 0, 0, state & 0x1 /* No token required for TEST_LOCKED states*/ );
        wait_dai_op_idle(0);

        uint32_t act_state = lsu_read_32(LC_CTRL_LC_STATE_OFFSET);
        uint32_t exp_state = calc_lc_state_mnemonic(state);
        if (act_state != exp_state) {
            VPRINTF(LOW, "ERROR: incorrect state: exp: %08X, act: %08X\n", act_state, exp_state);
            exit(1);
        }
    }
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
    
    lcc_initialization();    
    grant_mcu_for_fc_writes(); 
    
    transition_state_check(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);
    
    initialize_otp_controller();

    iterate_test_unlock_states();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
