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
#include <stdbool.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"

// This test runs without the PPD (Physical Presence Detect) pin being asserted,
// because we neither set it through the TB services route nor by writing the
// magic address that is monitored by lc_ctrl_bfm.
//
// The test tries to transfer to SCRAP, passing a zero token. When lc_ctrl_fsm
// tries to increment the LC counter, the transition will drop out, setting the
// FSM to PostTransSt and asserting state_invalid_error_o, which causes the
// STATE_ERROR in the STATUS register to be set.

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

bool body(void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    lcc_initialization();

    uint8_t lc_state_before = read_lc_state();
    uint8_t lc_cnt_before   = read_lc_counter();

    VPRINTF(LOW, "INFO: current lc state: %d\n", lc_state_before);
    VPRINTF(LOW, "INFO: current lc cntc state: %d\n", lc_cnt_before);

    // Check that the transition counter isn't at its maximum. That shouldn't
    // happen in this test because we only do one transition, but it can't hurt
    // to print something helpful if it goes wrong.
    if (lc_cnt_before == 24) {
        VPRINTF(LOW, "ERROR: Unexpectedly saturated LC transition counter.\n");
        return false;
    }

    // Try to transition to the SCRAP state, with no token. This should report
    // failure, then transition_state will inject a reset.
    if (!transition_state(SCRAP, NULL, true)) return false;
    if (!wait_dai_op_idle(0)) return false;

    // Check that the lifecycle state really has stayed at the version we
    // started with.
    if (!check_lc_state("previous state", lc_state_before)) return false;

    VPRINTF(LOW, "INFO: Test complete.");
    return true;
}

void main (void) {
    bool test_passed = body();
    mcu_sleep(160);
    SEND_STDOUT_CTRL(test_passed ? TB_CMD_TEST_PASS : TB_CMD_TEST_FAIL);
}
