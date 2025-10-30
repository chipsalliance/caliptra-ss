// SPDX-License-Identifier: Apache-2.0
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

// Do a single step of the transition loop. Return -1 on an error, 0
// if the test is complete, and 1 if the test should continue.
unsigned do_iteration(void) {
    uint32_t invalid_token[4] = {0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff};
    uint32_t buf[NUM_LC_STATES] = {0};

    lcc_initialization();
    force_PPD_pin();

    uint32_t lc_state_curr = read_lc_state();
    uint32_t lc_cnt_curr = read_lc_counter();
    uint32_t lc_cnt_next = lc_cnt_curr + 1;

    VPRINTF(LOW, "INFO: current lcc state: %d\n", lc_state_curr);
    VPRINTF(LOW, "INFO: current lc cntc state: %d\n", lc_cnt_curr);

    unsigned count = get_possible_next_states(buf);

    if (!count) {
        VPRINTF(LOW, "INFO: Test complete. No state should be reachable from current state\n");
        return 0;
    }

    uint32_t lc_state_next = buf[xorshift32() % count];
    VPRINTF(LOW, "INFO: next lcc state: %d\n", lc_state_next);

    lc_token_type_t token_type = trans_matrix[lc_state_curr][lc_state_next];

    VPRINTF(LOW, "Info: Using a wrong token\n");
    transition_state(lc_state_next,
                     token_type == ZER ? NULL : invalid_token,
                     true);

    if (lc_state_next != SCRAP && token_type == ZER) {
        if (!wait_dai_op_idle(0)) return -1;

        lc_state_curr = read_lc_state();
        if (lc_state_curr != lc_state_next) {
            VPRINTF(LOW, "ERROR: incorrect state: exp: %d, act: %d\n", lc_state_next, lc_state_curr);
            return -1;
        }
        lc_cnt_curr = read_lc_counter();
        if (lc_cnt_curr != lc_cnt_next) {
            VPRINTF(LOW, "ERROR: incorrect counter: exp: %d, act: %d\n", lc_cnt_next, lc_cnt_curr);
            return -1;
        }
    }

    return 1;
}

bool body (void) {
    // Randomly choose the next LC state among the all valid ones
    // based on the current state and repeat this until the SCRAP
    // state is reached.
    for (;;) {
        switch (do_iteration()) {
        case 0:
            return true;
        case -1:
            return false;
        default:
            break;
        }
    }
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    mcu_cptra_init_d();
    bool failed = !wait_dai_op_idle(0);

    if (!failed) failed = !body();

    SEND_STDOUT_CTRL(failed ? TB_CMD_TEST_FAIL : TB_CMD_TEST_PASS);
}
