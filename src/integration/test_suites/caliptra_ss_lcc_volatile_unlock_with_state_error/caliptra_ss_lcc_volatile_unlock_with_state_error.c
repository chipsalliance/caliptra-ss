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

// Coverage test for mci_lcc_st_trans.sv line 172:
//   if (lcc_volatile_raw_unlock_success_i && !(lcc_valid_SCRAP_req || state_error))
//
// This test hits the FALSE branch by forcing state_error HIGH via BFM
// while performing a volatile raw unlock. The MCI translator FSM should
// stay in TRANSLATOR_NON_DEBUG despite the successful volatile unlock,
// keeping security_state_o = {DEVICE_PRODUCTION, debug_locked=1}.

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    lcc_initialization();
    grant_mcu_for_fc_writes();

    // Verify initial state is RAW (FSM is in TRANSLATOR_NON_DEBUG)
    if (!check_lc_state("RAW", RAW)) {
        handle_error("ERROR: lcc is not in RAW state\n");
    }

    // Force state_error HIGH via BFM before initiating volatile unlock
    VPRINTF(LOW, "Forcing state_error HIGH via BFM\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_MCI_FORCE_STATE_ERROR);
    mcu_sleep(100);

    // In volatile raw unlock mode the token has to be passed in hashed form.
    const uint32_t hashed_raw_unlock_token[4] = {
        0xf0930a4d, 0xde8a30e6, 0xd1c8cbba, 0x896e4a11
    };

    // Obtain mutex to be able to write to the LCC CSRs.
    const uint32_t claim_trans_val = 0x96;
    uint32_t reg_value, loop_ctrl = 0;
    while (loop_ctrl != claim_trans_val) {
        lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, claim_trans_val);
        reg_value = lsu_read_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET);
        loop_ctrl = reg_value & claim_trans_val;
    }

    // Activate volatile raw unlock mode.
    lsu_write_32(SOC_LC_CTRL_TRANSITION_CTRL, 0x2);

    // Submit the volatile raw unlock transition to TEST_UNLOCKED0.
    // LCC will pulse lcc_volatile_raw_unlock_success_i, but since
    // state_error is forced HIGH, the MCI translator FSM condition
    // at line 172 evaluates FALSE and the FSM stays in TRANSLATOR_NON_DEBUG.
    if (!start_state_transition(TEST_UNLOCKED0, hashed_raw_unlock_token, false)) {
        // Release state_error before failing
        lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_MCI_RELEASE_STATE_ERROR);
        handle_error("ERROR: Unexpected failure when starting state transition.\n");
    }

    // At the LCC level, the volatile unlock succeeded and the LC state
    // reports TEST_UNLOCKED0. But the MCI translator blocked the debug
    // unlock due to state_error.
    if (!check_lc_state("TEST_UNLOCKED0", TEST_UNLOCKED0)) {
        lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_MCI_RELEASE_STATE_ERROR);
        handle_error("ERROR: LC state is not TEST_UNLOCKED0 after volatile unlock\n");
    }

    VPRINTF(LOW, "Volatile unlock succeeded at LCC level but MCI translator stayed locked (state_error active)\n");

    // Release state_error
    VPRINTF(LOW, "Releasing state_error via BFM\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_MCI_RELEASE_STATE_ERROR);
    mcu_sleep(100);

    // Reset FC/LCC and verify we return to RAW (volatile = no OTP write)
    reset_fc_lcc_rtl();
    lcc_initialization();
    if (!check_lc_state("RAW", RAW)) {
        handle_error("ERROR: LC state did not revert to RAW after reset\n");
    }

    mcu_sleep(160);

    SEND_STDOUT_CTRL(0xff);
}
