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


static uint32_t tokens[13][4] = {
    [RAU] = {CPTRA_SS_LC_CTRL_RAW_UNLOCK_TOKEN},              // RAW_UNLOCK
    [TU1] = {0x72f04808, 0x05f493b4, 0x7790628a, 0x318372c8}, // TEST_UNLOCKED1
    [TU2] = {0x17c78a78, 0xc7b443ef, 0xd6931045, 0x55e74f3c}, // TEST_UNLOCKED2
    [TU3] = {0x1644aa12, 0x79925802, 0xdbc26815, 0x8597a5fa}, // TEST_UNLOCKED3
    [TU4] = {0x34d1ea6e, 0x121f023f, 0x6e9dc51c, 0xc7439b6f}, // TEST_UNLOCKED4
    [TU5] = {0x03fd9df1, 0x20978af4, 0x49db216d, 0xb0225ece}, // TEST_UNLOCKED5
    [TU6] = {0xcfc0871c, 0xc400e922, 0x4290a4ad, 0x7f10dc89}, // TEST_UNLOCKED6
    [TU7] = {0x67e87f3e, 0xae6ee167, 0x802efa05, 0xbaaa3138}, // TEST_UNLOCKED7
    [TEX] = {0x2f533ae9, 0x341d2478, 0x5f066362, 0xb5fe1577}, // TEST_EXIT
    [DEX] = {0xf622abb6, 0x5d8318f4, 0xc721179d, 0x51c001f2}, // DEV_EXIT
    [PEX] = {0x25b8649d, 0xe7818e5b, 0x826d5ba4, 0xd6b633a0}, // PROD_EXIT
    [RMU] = {0x72f04808, 0x05f493b4, 0x7790628a, 0x318372c8}, // RMA
    [ZER] = {0}                                               // ZERO
};

// Return a random value (using xorshift32) from the range [lo, hi]. This is
// assumed to be nonempty (so lo <= hi).
unsigned sample_from_interval(unsigned lo, unsigned hi) {
    return lo + (xorshift32() % (hi - lo + 1));
}

bool body (void) {
    
    
    if (!check_lc_state("RAW", RAW)) return false;

    uint32_t lc_state_curr = read_lc_state();
    uint32_t lc_cnt_curr = read_lc_counter();

    VPRINTF(LOW, "INFO: current lcc state: %d\n", lc_state_curr);
    VPRINTF(LOW, "INFO: current lc cntc state: %d\n", lc_cnt_curr);

    if (lc_cnt_curr == 24) {
        VPRINTF(LOW, "INFO: reached max. LC counter value, finish test\n");
        return true;
    }

    uint32_t lc_state_next = (xorshift32() % 16)+2; //Eclude RAW and SCRAP states and TEST_UNLOCKED0, RAW states.
    lc_token_type_t token_type = trans_matrix[lc_state_curr][lc_state_next];

    // Obtain mutex to be able to write to the LCC CSRs.
    const uint32_t claim_trans_val = 0x96;
    uint32_t reg_value, loop_ctrl;
    while (loop_ctrl != claim_trans_val) {
        lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, claim_trans_val);
        reg_value = lsu_read_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET);
        loop_ctrl = reg_value & claim_trans_val;
    }

    // Activate volatile raw unlock mode.
    lsu_write_32(SOC_LC_CTRL_TRANSITION_CTRL, 0x2);

    // Request a transition into the chosen target state. This should fail.
    if (!transition_state(lc_state_next, 
            tokens[0], // Always use RAW_UNLOCK token
             true))
        return false;

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // The transition_state function should have finished up with a reset. After
    // that, the LCC should have reverted back to the RAW state.
    return check_lc_state("RAW", RAW);
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    lcc_initialization();
    grant_mcu_for_fc_writes();

    bool test_passed = body();

    mcu_sleep(160);

    SEND_STDOUT_CTRL(test_passed ? TB_CMD_TEST_PASS : TB_CMD_TEST_FAIL);
}
