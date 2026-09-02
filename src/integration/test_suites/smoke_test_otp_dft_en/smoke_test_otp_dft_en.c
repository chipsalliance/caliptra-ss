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
//
// smoke_test_otp_dft_en
//
// Checks the fuse macro wrapper DFT enable output (cptra_ss_otp_dft_en_o) across
// a RAW -> TEST_UNLOCKED0 -> RMA life cycle walk.
//
// The output is high only when all three qualifiers hold: the OTP life cycle
// state is valid, the LCC has granted SOC_DFT_EN, and the steady state is not
// RMA. That yields:
//
//   RAW            -> low  (LCC does not grant DFT in RAW)
//   TEST_UNLOCKED0 -> high (DFT granted, state valid, not RMA)
//   RMA            -> low  (explicitly blocked even though the LCC grants DFT)
//
// The RMA case is the interesting one: the LCC still asserts DFT_EN in RMA, so
// a low output there proves the RMA qualifier is doing its job rather than the
// signal merely tracking SOC_DFT_EN.
//
// The signal is an RTL output with no register view, so the checks are issued
// as TB service commands (CMD_OTP_DFT_EN_EXPECT_LOW/HIGH); the testbench samples
// the pin and fails the test directly on a mismatch.

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

// RAW -> TEST_UNLOCKED0 uses the raw unlock token; TEST_UNLOCKED0 -> RMA uses
// the all-zero token (see trans_matrix in libs/lc_ctrl).
static uint32_t raw_unlock_tok[4] = {CPTRA_SS_LC_CTRL_RAW_UNLOCK_TOKEN};
static uint32_t zero_tok[4]       = {0};

static void expect_dft_en(bool expected_high, const char *where) {
    // Let the LCC decode settle before sampling: otp_state_valid_o needs a cycle
    // after the state read-out, and cptra_ss_otp_dft_en_o is registered on top.
    mcu_sleep(256);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT,
                 expected_high ? CMD_OTP_DFT_EN_EXPECT_HIGH : CMD_OTP_DFT_EN_EXPECT_LOW);
    VPRINTF(LOW, "MCU: [%s] expecting otp_dft_en = %d\n", where, expected_high ? 1 : 0);
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU: fuse macro DFT enable smoke test\n=================\n\n");

    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    lcc_initialization();

    // ---- RAW: fuse macro debug must be closed ----
    uint32_t lc_state = read_lc_state();
    if (lc_state != RAW) {
        handle_error("ERROR: expected to start in RAW, actual lc state %d\n", lc_state);
    }
    VPRINTF(LOW, "MCU: in RAW\n");
    expect_dft_en(false, "RAW");

    // ---- RAW -> TEST_UNLOCKED0: fuse macro debug opens ----
    transition_state(TEST_UNLOCKED0, raw_unlock_tok, false);
    wait_dai_op_idle(0);
    lcc_initialization();

    lc_state = read_lc_state();
    if (lc_state != TEST_UNLOCKED0) {
        handle_error("ERROR: expected TEST_UNLOCKED0, actual lc state %d\n", lc_state);
    }
    VPRINTF(LOW, "MCU: in TEST_UNLOCKED0\n");
    expect_dft_en(true, "TEST_UNLOCKED0");

    // ---- TEST_UNLOCKED0 -> RMA: fuse macro debug closes again ----
    force_PPD_pin();
    transition_state(RMA, zero_tok, false);
    wait_dai_op_idle(0);
    lcc_initialization();

    lc_state = read_lc_state();
    if (lc_state != RMA) {
        handle_error("ERROR: expected RMA, actual lc state %d\n", lc_state);
    }
    VPRINTF(LOW, "MCU: in RMA\n");
    expect_dft_en(false, "RMA");

    VPRINTF(LOW, "MCU: fuse macro DFT enable smoke test PASSED\n");

    mcu_sleep(160);
    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
}
