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
#include <stdbool.h>
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

// The body of the test. After initialisation, check the current LC state, pick a new LC state that
// is impossible to transition to and try to transition to it.
void body(void)
{
    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    lcc_initialization();
    force_PPD_pin();

    // Read the LC_STATE register to get the current LC state, then LC_TRANSITION_COUNT (giving
    // the number of lifecycle transitions that have happened so far).
    uint32_t cur_lc_state = read_lc_state();
    uint32_t transition_count = read_lc_counter();

    VPRINTF(LOW, "INFO: current LC state: %d (have seen %d transitions)\n",
            cur_lc_state, transition_count);

    if (transition_count >= 24) {
        VPRINTF(LOW, "INFO: reached max. LC counter value. End test.\n");
        return;
    }

    if (cur_lc_state == SCRAP) {
        VPRINTF(LOW, "INFO: reached LC SCRAP state. End test.\n");
        return;
    }

    // Search through LC states strictly after this one, finding the ones that can't be reached
    // (because the entry in the transition matrix is INV).
    //
    // Store the indices of the states into buf and the number of entries in inv_count.
    uint32_t inv_count = 0;
    uint32_t buf[NUM_LC_STATES];

    for (uint32_t i = 1; i + cur_lc_state < NUM_LC_STATES; i++)
        if (trans_matrix[cur_lc_state][i + cur_lc_state] == INV)
            buf[inv_count++] = i + cur_lc_state;

    // We might not have actually found any states, because we might be in the RMA state, which can
    // transition to SCRAP with a zero token and has no other state that is later. If that has
    // happened, end the test.
    if (!inv_count) {
        VPRINTF(LOW, "INFO: Ending test as there is no INV state after %d\n", cur_lc_state);
        return;
    }

    // Pick a random state that we can't transition to (because the entry in the transition matrix
    // is INV)
    uint32_t lc_state_next = buf[xorshift32() % inv_count];
    VPRINTF(LOW, "INFO: target LC state: %d\n", lc_state_next);

    // Request the transition, passing a zero token (since no token is valid anyway) and expecting
    // an error to come out.
    uint32_t zero_token[4] = {0, 0, 0, 0};
    transition_state(lc_state_next, zero_token, true);
    wait_dai_op_idle(0);

    uint32_t new_lc_state = read_lc_state();

    // Check that the transition request was handled, which is either shown by the lifecycle state
    // staying unchanged or by it jumping to the terminal PostTrans state. That, in turn, can be
    // seen in the lc_state register, which should now read as cur_lc_state or POST_TRANSITION. The
    // latter is a repetition of the the 5-bit DecLcStPostTrans value (defined in
    // lc_ctrl_state_pkg.sv), which is 21.
    if (new_lc_state != cur_lc_state && new_lc_state != 21) {
        VPRINTF(LOW,
                ("ERROR: Transition request has not moved us to POST_TRANSITION. "
                 "The underlying LC state is %d, not %d or 21.\n"),
                new_lc_state, cur_lc_state);
        return;
    }

    VPRINTF(LOW, "Info: Test OK\n");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    body();

    for (uint8_t i = 0; i < 160; i++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
