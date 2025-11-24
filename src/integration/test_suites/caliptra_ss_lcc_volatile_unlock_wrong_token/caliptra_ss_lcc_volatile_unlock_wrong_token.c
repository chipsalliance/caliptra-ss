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

// A bogus token to use when requesting a transition from RAW to TEST_UNLOCKED0.
static const uint32_t bad_token[4] = {
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff
};

bool body (void) {
    if (!check_lc_state("RAW", RAW)) return false;

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

    // Request a transition into TEST_UNLOCKED0, but pass a bad token. This
    // should fail.
    if (!transition_state(TEST_UNLOCKED0), bad_token, true) return false;

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
