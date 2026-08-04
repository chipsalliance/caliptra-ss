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

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"
#include "soc_ifc.h"

volatile char *stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

static const uint32_t k_test_unlock1_token[4] = {
    0x72f04808, 0x05f493b4, 0x7790628a, 0x318372c8
};

static void check_ss_debug_intent_high(void) {
    uint32_t debug_intent = lsu_read_32(SOC_MCI_TOP_MCI_REG_SS_DEBUG_INTENT);
    if ((debug_intent & MCI_REG_SS_DEBUG_INTENT_DEBUG_INTENT_MASK) == 0) {
        handle_error("ERROR: SS_DEBUG_INTENT bit0 is not high\n");
    }
}

static void require_lc_state(uint8_t expected, const char *desc) {
    uint8_t actual = read_lc_state();
    if (actual != expected) {
        VPRINTF(LOW, "ERROR: LC state mismatch for %s: exp=%d act=%d\n",
                desc, expected, actual);
        handle_error("ERROR: unexpected LC state\n");
    }
}

void main(void) {
    VPRINTF(LOW, "=======================================\n"
                 "MCU debug-intent LC transition test\n"
                 "=======================================\n\n");

    mcu_cptra_init_d();
    wait_dai_op_idle(0);
    lcc_initialization();

    check_ss_debug_intent_high();
    require_lc_state(TEST_UNLOCKED0, "initial state");

    VPRINTF(LOW, "INFO: Attempting zero-token TEST_UNLOCKED0 -> TEST_LOCKED0\n");
    read_lc_counter();
    if (!start_state_transition(TEST_LOCKED0, NULL, false)) {
        handle_error("ERROR: zero-token LC transition failed under debug intent\n");
    }
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);
    require_lc_state(TEST_LOCKED0, "after zero-token transition");

    VPRINTF(LOW, "INFO: Attempting token-dependent TEST_LOCKED0 -> TEST_UNLOCKED1\n");
    if (!start_state_transition(TEST_UNLOCKED1, k_test_unlock1_token, false)) {
        handle_error("ERROR: token-dependent LC transition failed under debug intent\n");
    }
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);
    require_lc_state(TEST_UNLOCKED1, "after token transition");

    SEND_STDOUT_CTRL(0xff);
}
