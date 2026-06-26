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
//
// Test: mci_lcc_volatile_unlock_with_state_error
//
// Transitions the device RAW -> volatile TEST_UNLOCKED0 state with
// state error active should result in debug being locked and device should remain
// in PRODUCTION state.
//
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

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

#define LIFECYCLE_PRODUCTION     (0x3u)

void main(void) {
    // In volatile raw unlock mode the token has to be passed in hashed form.
    const uint32_t hashed_raw_unlock_token[4] = {
        0xf0930a4d, 0xde8a30e6, 0xd1c8cbba, 0x896e4a11
    };

    VPRINTF(LOW, "=================\nMCU mci_lcc_volatile_unlock_with_state_error\n=================\n\n");

    lcc_initialization();
    // Inject state_error.
    VPRINTF(LOW, "INFO: injecting state_error into MCI LCC state translator\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_MCI_LCC_INJECT_STATE_ERROR);

    // RAW volatile unlock
    // Obtain mutex to be able to write to the LCC CSRs.
    const uint32_t claim_trans_val = 0x96;
    uint32_t reg_value, loop_ctrl, state;
    while (loop_ctrl != claim_trans_val) {
        lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, claim_trans_val);
        reg_value = lsu_read_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET);
        loop_ctrl = reg_value & claim_trans_val;
    }

    // Activate volatile raw unlock mode.
    lsu_write_32(SOC_LC_CTRL_TRANSITION_CTRL, 0x2);

    // Transition into the TEST_UNLOCKED0 state.
    start_state_transition(TEST_UNLOCKED0, hashed_raw_unlock_token, false);

    state = lsu_read_32(SOC_LC_CTRL_LC_STATE);
    if (!check_lc_state("TEST_UNLOCKED0", TEST_UNLOCKED0)) {
        VPRINTF(LOW, "ERROR: lcc is not in test unlocked0 state\n");
        SEND_STDOUT_CTRL(0x01);
        return;
    }

    for (uint8_t i = 0; i < 160; i++) {
        __asm__ volatile ("nop");
    }

    uint32_t sec_state = lsu_read_32(SOC_MCI_TOP_MCI_REG_SECURITY_STATE);
    uint32_t lifecycle = sec_state & MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_MASK;
    if (lifecycle != LIFECYCLE_PRODUCTION || (sec_state & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK) == 0) {
        VPRINTF(LOW, "ERROR: expected LIFECYCLE_PRODUCTION(0x%x) in TRANSLATOR_NON_DEBUG state, got lifecycle=0x%x (SECURITY_STATE=0x%08x)\n",
                LIFECYCLE_PRODUCTION, lifecycle, sec_state);
        SEND_STDOUT_CTRL(0x01);
        return;
    }

    SEND_STDOUT_CTRL(0xff);
    while(1);
}
