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
#include <stddef.h>

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


bool test_all_lc_transitions_no_RMA_no_SCRAP(void) {

    // Example token for the Raw->TestUnlocked0 jump (128 bits).
    // Adjust to match your real raw-unlock token if needed.
    uint32_t token_value = 1;
    // We start at index0=0 (Raw). We do transitions *from* each state
    // to the *next* in the sequence. So we loop from i=0 to i=(N-2).
    for (int i = 0; i < NUM_LC_STATES - 3; i++) {
        uint32_t from_state = state_sequence[i];
        uint32_t to_state   = state_sequence[i+1];
        VPRINTF(LOW, "\n=== Transition from %08d to %08d ===\n",
                from_state, to_state);

        const uint32_t zero_token[4] = {0, 0, 0, 0};
        const uint32_t rep_token[4] = {token_value, token_value,
                                       token_value, token_value};

        const uint32_t *backing_token;
        if (i == 0) backing_token = raw_unlock_token;
        else if (i < 15) backing_token = zero_token;
        else {
            backing_token = rep_token;
            ++token_value;
        }

        if (!transition_state(to_state, use_token[i+1] ? backing_token : NULL)) return false;
        reset_fc_lcc_rtl();
    }

    VPRINTF(LOW, "All transitions complete.\n");
    return true;
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU: Caliptra Boot Go\n=================\n\n");    
    mcu_cptra_init_d(.cfg_skip_set_fuse_done=true);
    force_lcc_tokens();
    VPRINTF(LOW, "=========\nMCU: TESTING LCC STATE TRANS FROM RAW to PROD_END\n=================\n\n");   

    bool passed = test_all_lc_transitions_no_RMA_no_SCRAP();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(passed ? TB_CMD_TEST_PASS : TB_CMD_TEST_FAIL);
}
