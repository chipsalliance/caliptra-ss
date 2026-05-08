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

// A test to check the volatile raw unlock state transition works
// properly.
//
// - Enable the lc_sec_volatile_raw_unlock_en_i input to lc_ctrl (with
//   the SOC_LC_CTRL_TRANSITION_CTRL backdoor method)
//
// - Try to transition to the TEST_UNLOCKED0 state without injecting
//   the reset one normally needs.
//
// - Reset and check that we are back in RAW.

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

/**
 * A test to verify that the volatile raw unlock state transition is working.
 */
bool body (void) {
    // In volatile raw unlock mode the token has to be passed in hashed form.
    const uint32_t hashed_raw_unlock_token[4] = {
        0xf0930a4d, 0xde8a30e6, 0xd1c8cbba, 0x896e4a11
    };

    if (!check_lc_state("RAW", RAW)) {
        VPRINTF(LOW, "ERROR: lcc is not in raw state\n");
        return false;
    }

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

    // Transition into the TEST_UNLOCKED0 state. This uses
    // start_state_transition, which (unlike transition_state) doesn't perform a
    // reset.
    if (!start_state_transition(TEST_UNLOCKED0, hashed_raw_unlock_token, false)) {
        VPRINTF(LOW, "ERROR: Unexpected failure when starting state transition.\n");
        return false;
    }

    // At this point, the volatile raw unlock pathway will have left us in the
    // TEST_UNLOCKED0 state. Check this has happened (and we haven't ended up in
    // POST_TRANSITION).
    if (!check_lc_state("TEST_UNLOCKED0", TEST_UNLOCKED0)) return false;

    // To check that this really was a "volatile" change, inject a reset. The
    // lifecycle state should be back to RAW (rather than e.g. TEST_UNLOCKED0)
    reset_fc_lcc_rtl();
    lcc_initialization();
    if (!check_lc_state("RAW", RAW)) return false;

    return true;
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
