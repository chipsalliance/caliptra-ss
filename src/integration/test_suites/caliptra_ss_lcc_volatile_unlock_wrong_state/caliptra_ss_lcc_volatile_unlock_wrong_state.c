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
void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")

    // In volatile raw unlock mode the token has to be passed in hashed form.
    const uint32_t unhashed_raw_unlock_token[4] = {
        0x3c8ff2b6, 0x1e213794, 0x358f685c, 0x4748d3f5
    };

    const raw_state = calc_lc_state_mnemonic(RAW);
    uint32_t next_state = TEST_LOCKED0 + xorshift32() % (SCRAP - TEST_LOCKED0 + 1);
    const post_trans_state = calc_lc_state_mnemonic(21);
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes();

    uint32_t state = lsu_read_32(SOC_LC_CTRL_LC_STATE);
    if (state != raw_state) {
        VPRINTF(LOW, "ERROR: lcc is not in raw state\n");
        goto epilogue;
    }

    VPRINTF(LOW, "Info: Trying to perfrom a volatile unlock from RAW to state %d!\n", next_state);

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

    // Transition into the state.
    sw_transition_req_with_expec_error(
        calc_lc_state_mnemonic(next_state),
        unhashed_raw_unlock_token[0],
        unhashed_raw_unlock_token[1],
        unhashed_raw_unlock_token[2],
        unhashed_raw_unlock_token[3],
        1
    );

    state = lsu_read_32(SOC_LC_CTRL_LC_STATE);
    if (state != post_trans_state) {
        VPRINTF(LOW, "ERROR: lcc is not in post_trans state\n");
        goto epilogue;
    }

    // After a reset, the LCC should have reverted back to the RAW state.
    reset_fc_lcc_rtl();
    lcc_initialization();

    state = lsu_read_32(SOC_LC_CTRL_LC_STATE);
    if (state != raw_state) {
        VPRINTF(LOW, "ERROR: lcc is not in raw state\n");
    };

epilogue:
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
