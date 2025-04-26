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
#include "fuse_ctrl_address_map.h"
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

static uint32_t invalid_tokens[13][4] = {
    [RAU] = {0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff}, // RAW_UNLOCK
    [TU1] = {0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff}, // TEST_UNLOCKED1
    [TU2] = {0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff}, // TEST_UNLOCKED2
    [TU3] = {0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff}, // TEST_UNLOCKED3
    [TU4] = {0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff}, // TEST_UNLOCKED4
    [TU5] = {0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff}, // TEST_UNLOCKED5
    [TU6] = {0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff}, // TEST_UNLOCKED6
    [TU7] = {0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff}, // TEST_UNLOCKED7
    [TEX] = {0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff}, // TEST_EXIT
    [DEX] = {0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff}, // DEV_EXIT
    [PEX] = {0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff}, // PROD_EXIT
    [RMU] = {0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff}, // RMA
    [ZER] = {0}                                               // ZERO
};
void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    uint32_t buf[NUM_LC_STATES] = {0};

    // Randomly choose the next LC state among the all valid ones
    // based on the current state and repeat this until the SCRAP
    // state is reached.
    while (1) {
        lcc_initialization();
        force_PPD_pin();

        uint32_t lc_state_curr = read_lc_state();
        uint32_t lc_cnt_curr = read_lc_counter();
        uint32_t lc_cnt_next = lc_cnt_curr + 1; 

        VPRINTF(LOW, "INFO: current lcc state: %d\n", lc_state_curr);
        VPRINTF(LOW, "INFO: current lc cntc state: %d\n", lc_cnt_curr);

        uint32_t count = 0;
        memset(buf, 0, sizeof(buf));
        for (uint32_t i = 1, k = 0; (i + lc_state_curr)< NUM_LC_STATES; i++) {
            if (trans_matrix[lc_state_curr][i+lc_state_curr] != INV) {
                buf[count] = i + lc_state_curr;
                count++;
            }
        }

        if (count) {
            uint32_t lc_state_next = buf[xorshift32() % count];
            VPRINTF(LOW, "INFO: next lcc state: %d\n", lc_state_next);

            lc_token_type_t token_type = trans_matrix[lc_state_curr][lc_state_next];
            transition_state_req_with_expec_error(lc_state_next,
                             invalid_tokens[token_type][0],
                             invalid_tokens[token_type][1],
                             invalid_tokens[token_type][2],
                             invalid_tokens[token_type][3],
                             token_type != ZER);

            wait_dai_op_idle(0);

            uint32_t lc_state_after_transition = read_lc_state();
            VPRINTF(LOW, "lc_state_curr %d, lc_state_after_transition %d\n", lc_state_curr, lc_state_after_transition);
            // Check if we are still in RAW state.
            if (lc_state_after_transition != lc_state_curr) {
                VPRINTF(LOW, "ERROR: incorrect state: exp: %d, act: %d\n", lc_state_curr, lc_state_after_transition);
                goto epilogue;
            }
            lc_cnt_curr = read_lc_counter();
            // Check if the counter got incremented.
            if (lc_cnt_curr != lc_cnt_next) {
                VPRINTF(LOW, "ERROR: incorrect counter: exp: %d, act: %d\n", lc_cnt_next, lc_cnt_curr);
                goto epilogue;
            }
            VPRINTF(LOW, "INFO: test completed, terminating test\n");
            goto epilogue; 
        }
    }
    
epilogue:
    for (uint8_t i = 0; i < 160; i++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
