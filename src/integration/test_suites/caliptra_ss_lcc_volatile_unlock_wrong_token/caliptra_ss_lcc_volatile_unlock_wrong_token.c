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
 * A test to verify that the volatile raw unlock state transition is working.
 */
bool body (void) {
    // In volatile raw unlock mode the token has to be passed in hashed form.
    const uint32_t unhashed_raw_unlock_token_wrong[4] = {
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff
    };

    const raw_state = calc_lc_state_mnemonic(RAW);
    const test_unlocked0_state = calc_lc_state_mnemonic(TEST_UNLOCKED0);
    const post_trans_state = calc_lc_state_mnemonic(21);
    
    uint32_t state = lsu_read_32(SOC_LC_CTRL_LC_STATE);
    if (state != raw_state) {
        VPRINTF(LOW, "ERROR: lcc is not in raw state\n");
        return false;
    }

    // Obtain mutex to be able to write to the LCC CSRs.
    claim_transition_mutex();

    // Activate volatile raw unlock mode.
    lsu_write_32(SOC_LC_CTRL_TRANSITION_CTRL, 0x2);

    // Transition into the TEST_UNLOCKED0 state.
    if (!sw_transition_req(calc_lc_state_mnemonic(TEST_UNLOCKED0),
                           unhashed_raw_unlock_token_wrong,
                           true))
        return false;

    state = lsu_read_32(SOC_LC_CTRL_LC_STATE);
    if (state != post_trans_state) {
        VPRINTF(LOW, "ERROR: lcc is not in post_trans state\n");
        return false;
    }

    // After a reset, the LCC should have reverted back to the RAW state.
    reset_fc_lcc_rtl();
    lcc_initialization();

    state = lsu_read_32(SOC_LC_CTRL_LC_STATE);
    if (state != raw_state) {
        VPRINTF(LOW, "ERROR: lcc is not in raw state\n");
        return false;
    };
}

void main (void) { fc_run_test(true, body); }
