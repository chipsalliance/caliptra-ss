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
//

#include <stdlib.h>
#include <stdint.h>

#include "soc_address_map.h"
#include "fuse_ctrl.h"
#include "printf.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "riscv_hw_if.h"
#include "lc_ctrl.h"

#define CLAIM_TRANS_VAL 0x96 // Tried to match MuBi8True

lc_token_type_t trans_matrix[NUM_LC_STATES][NUM_LC_STATES] = {
/*          RAW  TU0  TL0  TU1  TL1  TU2  TL2  TU3  TL3  TU4  TL4  TU5  TL5  TU6  TL6  TU7  DEV  PRD  PRE  RMA  SCR */
/* RAW */ { INV, RAU, INV, RAU, INV, RAU, INV, RAU, INV, RAU, INV, RAU, INV, RAU, INV, RAU, INV, INV, INV, INV, ZER },
/* TU0 */ { INV, INV, ZER, INV, ZER, INV, ZER, INV, ZER, INV, ZER, INV, ZER, INV, ZER, INV, TEX, DEX, PEX, ZER, ZER },
/* TL0 */ { INV, INV, INV, TU1, INV, TU2, INV, TU3, INV, TU4, INV, TU5, INV, TU6, INV, TU7, TEX, DEX, PEX, INV, ZER },
/* TU1 */ { INV, INV, INV, INV, ZER, INV, ZER, INV, ZER, INV, ZER, INV, ZER, INV, ZER, INV, TEX, DEX, PEX, ZER, ZER },
/* TL1 */ { INV, INV, INV, INV, INV, TU2, INV, TU3, INV, TU4, INV, TU5, INV, TU6, INV, TU7, TEX, DEX, PEX, INV, ZER },
/* TU2 */ { INV, INV, INV, INV, INV, INV, ZER, INV, ZER, INV, ZER, INV, ZER, INV, ZER, INV, TEX, DEX, PEX, ZER, ZER },
/* TL2 */ { INV, INV, INV, INV, INV, INV, INV, TU3, INV, TU4, INV, TU5, INV, TU6, INV, TU7, TEX, DEX, PEX, INV, ZER },
/* TU3 */ { INV, INV, INV, INV, INV, INV, INV, INV, ZER, INV, ZER, INV, ZER, INV, ZER, INV, TEX, DEX, PEX, ZER, ZER },
/* TL3 */ { INV, INV, INV, INV, INV, INV, INV, INV, INV, TU4, INV, TU5, INV, TU6, INV, TU7, TEX, DEX, PEX, INV, ZER },
/* TU4 */ { INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, ZER, INV, ZER, INV, ZER, INV, TEX, DEX, PEX, ZER, ZER },
/* TL4 */ { INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, TU5, INV, TU6, INV, TU7, TEX, DEX, PEX, INV, ZER },
/* TU5 */ { INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, ZER, INV, ZER, INV, TEX, DEX, PEX, ZER, ZER },
/* TL5 */ { INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, TU6, INV, TU7, TEX, DEX, PEX, INV, ZER },
/* TU6 */ { INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, ZER, INV, TEX, DEX, PEX, ZER, ZER },
/* TL6 */ { INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, TU7, TEX, DEX, PEX, INV, ZER },
/* TU7 */ { INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, TEX, DEX, PEX, ZER, ZER },
/* DEV */ { INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, DEX, PEX, RMU, ZER },
/* PRD */ { INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, PEX, RMU, ZER },
/* PRE */ { INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, ZER },
/* RMA */ { INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, ZER },
/* SCR */ { INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV, INV }
};

// The *decoded* enumeration values you gave in the source code
// LcStRaw=0, LcStTestUnlocked0=1, LcStTestLocked0=2, etc.
// The final step is to go to Scrap (20).
// (We skip any special RMA strap toggling here; add it if needed.)
uint32_t state_sequence[] = {
    0,  // LcStRaw
    1,  // LcStTestUnlocked0
    2,  // LcStTestLocked0
    3,  // LcStTestUnlocked1
    4,  // LcStTestLocked1
    5,  // LcStTestUnlocked2
    6,  // LcStTestLocked2
    7,  // LcStTestUnlocked3
    8,  // LcStTestLocked3
    9,  // LcStTestUnlocked4
    10, // LcStTestLocked4
    11, // LcStTestUnlocked5
    12, // LcStTestLocked5
    13, // LcStTestUnlocked6
    14, // LcStTestLocked6
    15, // LcStTestUnlocked7
    16, // LcStDev
    17, // LcStProd
    18, // LcStProdEnd
    19, // LcStRma
    20  // LcStScrap
};

// If you only need tokens on the very first transition (Raw -> TestUnlocked0),
// we can store a parallel “bool” array to indicate usage.
// For instance, only use tokens for the 2nd element (transition *into* index1).
// Adjust as needed for real usage.
uint8_t use_token[] = {
    0, // from "no previous" to Raw
    1, // from Raw -> TestUnlocked0: real token
    0, // from TestUnlocked0 -> TestLocked0
    1, // ...
    0, // from TestUnlocked1 -> TestLocked1
    1,
    0, // from TestUnlocked2 -> TestLocked2
    1,
    0, // from TestUnlocked3 -> TestLocked3
    1,
    0, // from TestUnlocked4 -> TestLocked4
    1,
    0, // from TestUnlocked5 -> TestLocked5
    1,
    0, // from TestUnlocked6 -> TestLocked6
    1,
    1, // from TestUnlocked7 -> MANUF
    1, // from MANUF -> PROD
    1, // from PROD -> PROD_END
    1, // from PROD -> RMA
    0  // from PROD -> SCRAP
};

// Repeatedly read the lc_ctrl status register until all the bits in mask are set. desc is a
// human-readable description of what we are waiting for.
static void masked_wait_for_status(const char *desc, uint32_t mask)
{
    uint32_t reg_value = 0;

    VPRINTF(LOW, "LC_CTRL: Reading lc_ctrl status, waiting for %s.\n", desc);
    while (mask &~ reg_value) {
        VPRINTF(LOW, "DEBUG: Still waiting for bits in status: 0x%08x.\n", mask &~ reg_value);
        reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
    }
}
uint32_t raw_unlock_token[4] = {
    CPTRA_SS_LC_CTRL_RAW_UNLOCK_TOKEN
};

void lcc_initialization(void) {
    masked_wait_for_status("ready signal", CALIPTRA_SS_LC_CTRL_READY_MASK);
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is ready.\n");

    masked_wait_for_status("initialization", CALIPTRA_SS_LC_CTRL_INIT_MASK);
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is initialized.\n");
}

void force_lcc_tokens(void) {
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FORCE_LC_TOKENS);
    VPRINTF(LOW, "MCU: LCC TOKENs are forced to certain values!\n");
}

static void
start_transition_command(uint32_t next_lc_state, const uint32_t token[4])
{
    uint32_t reg_value;
    uint32_t status_val;
    uint32_t loop_ctrl;

    reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
    loop_ctrl = (reg_value & CALIPTRA_SS_LC_CTRL_INIT_MASK);

    while(!loop_ctrl) {
        VPRINTF(LOW, "Read Register [0x%08x]: 0x%08x anded with 0x%08x \n",
                LC_CTRL_STATUS_OFFSET, reg_value, CALIPTRA_SS_LC_CTRL_INIT_MASK);
        reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
        loop_ctrl = (reg_value & CALIPTRA_SS_LC_CTRL_INIT_MASK);
    }
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is initalized!\n");

    VPRINTF(LOW, "Starting sw_transition_req...\n");

    // Step 1: Set Claim Transition Register
    loop_ctrl = 0;
    while (loop_ctrl != CLAIM_TRANS_VAL) {
        lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, CLAIM_TRANS_VAL);
        reg_value = lsu_read_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET);
        loop_ctrl = reg_value & CLAIM_TRANS_VAL;
        VPRINTF(LOW, "Claim Mutex Register [0x%08x]: Read 0x%08x, expected 0x%08x\n",
                LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, reg_value, CLAIM_TRANS_VAL);
    }
    VPRINTF(LOW, "LC_CTRL: Mutex successfully acquired.\n");

    // Step 3: Set Target Lifecycle State
    VPRINTF(LOW, "Setting next lifecycle state [0x%08x]: 0x%08x\n", LC_CTRL_TRANSITION_TARGET_OFFSET, next_lc_state);
    lsu_write_32(LC_CTRL_TRANSITION_TARGET_OFFSET, next_lc_state);

    // Step 4: Write Transition Tokens
    if (token) {
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token[0]);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET, token[0]);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token[1]);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_1_OFFSET, token[1]);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token[2]);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_2_OFFSET, token[2]);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token[3]);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_3_OFFSET, token[3]);
    }

    // Step 6: Trigger the Transition Command
    VPRINTF(LOW, "Triggering transition command [0x%08x]: 0x1\n", LC_CTRL_TRANSITION_CMD_OFFSET);
    lsu_write_32(LC_CTRL_TRANSITION_CMD_OFFSET, 0x1);

    mcu_sleep(1000);
}

static bool
poll_transition_status(bool expected_fail)
{
    const char *expected_adj = expected_fail ? "Expected" : "Unexpected";
    const char *error_noun   = expected_fail ? "e**or" : "error";

    bool transition_successful = false;

    VPRINTF(LOW, "Polling status register [0x%08x]...\n", LC_CTRL_STATUS_OFFSET);
    while (1)
    {
        uint32_t status_val = lsu_read_32(LC_CTRL_STATUS_OFFSET);

        bool TRANSITION_SUCCESSFUL  = (status_val >> 3) & 1;
        bool TRANSITION_COUNT_ERROR = (status_val >> 4) & 1;
        bool TRANSITION_ERROR       = (status_val >> 5) & 1;
        bool TOKEN_ERROR            = (status_val >> 6) & 1;
        bool RMA_ERROR              = (status_val >> 7) & 1;
        bool OTP_ERROR              = (status_val >> 8) & 1;
        bool STATE_ERROR            = (status_val >> 9) & 1;
        bool BUS_INTG_ERROR         = (status_val >> 10) & 1;
        bool OTP_PARTITION_ERROR    = (status_val >> 11) & 1;

        if (TRANSITION_SUCCESSFUL) {
            if (expected_fail) {
                VPRINTF(LOW, "Error: Transition unexpectedly successful\n");
            } else {
                VPRINTF(LOW, "Transition successful.\n");
                transition_successful = true;
            }
            break;
        }

        const char *error_type = NULL;

        if (TRANSITION_ERROR) error_type = "transition";
        else if (TOKEN_ERROR) error_type = "token";
        else if (OTP_ERROR) error_type = "OTP";
        else if (RMA_ERROR) error_type = "RMA / RMA condition";
        else if (TRANSITION_COUNT_ERROR) error_type = "transition count";
        else if (STATE_ERROR) error_type = "state";
        else if (BUS_INTG_ERROR) error_type = "bus integrity";
        else if (OTP_PARTITION_ERROR) error_type = "OTP partition";

        if (error_type) {
            VPRINTF(LOW, "%s %s %s detected.\n", expected_adj, error_type, error_noun);
            break;
        }
    }

    return transition_successful ^ expected_fail;
}

static uint32_t calc_lc_state_mnemonic(uint8_t state) {
    uint32_t next_lc_state_5bit = state & 0x1F;
    uint32_t targeted_state_5 =
        (next_lc_state_5bit << 25) |
        (next_lc_state_5bit << 20) |
        (next_lc_state_5bit << 15) |
        (next_lc_state_5bit << 10) |
        (next_lc_state_5bit << 5)  |
        next_lc_state_5bit;
    return targeted_state_5;
}

// The guts of the transition request functions. The next_lc_state argument should be the "mnemonic"
// (replicated) version of the state value. The transition is expected to report success iff
// expected_fail is false.
static bool sw_transition_req_core(uint32_t next_lc_state, const uint32_t token[4], bool expected_fail)
{
    start_transition_command(next_lc_state, token);

    bool had_expected_behaviour = poll_transition_status(expected_fail);

    lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, 0x0);

    VPRINTF(LOW, "transition_req completed.\n");

    return had_expected_behaviour;
}

bool sw_transition_req(uint32_t next_lc_state, const uint32_t token[4])
{
    return sw_transition_req_core(next_lc_state, token, false);
}

bool transition_state(uint8_t next_lc_state, const uint32_t token[4])
{
    if (!sw_transition_req_core(calc_lc_state_mnemonic(next_lc_state), token, false)) return false;

    // The transition request succeeded, as expected. This means we've written
    // the new state to OTP, but now the lc_ctrl FSM has dropped into the
    // terminal PostTransSt. Inject a reset to "start again"
    reset_fc_lcc_rtl();

    return true;
}

bool transition_state_req_with_expec_error(uint8_t next_lc_state, const uint32_t token[4])
{
    if (!sw_transition_req_core(calc_lc_state_mnemonic(next_lc_state), token, true)) return false;

    // Although the transition request hasn't succeeded, it will have left the
    // lifecycle state INVALID. Inject a reset to "start again" (using the state
    // that was stored in fuses beforehand).
    reset_fc_lcc_rtl();

    return true;
}

bool transition_state_check(uint8_t next_lc_state, const uint32_t token[4]) {

    if (!transition_state(next_lc_state, token)) return false;

    wait_dai_op_idle(0);
    uint32_t lc_state_curr = read_lc_state();

    if (lc_state_curr != next_lc_state) {
        VPRINTF(LOW, "ERROR: incorrect state: exp: %d, act %d\n", next_lc_state, lc_state_curr);
        return false;
    }

    return true;
}

bool sw_transition_req_with_expec_error(uint32_t next_lc_state, const uint32_t token[4])
{
    return sw_transition_req_core(next_lc_state, token, true);
}

void force_PPD_pin(void) {
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_FORCE_RMA_SCRAP_PPD);
    VPRINTF(LOW, "MCU: RMA_SCRAP_PPD pin asserted high!\n");
}

uint8_t read_lc_state(void) {
    mcu_sleep(512);

    // Read LC_CTRL_LC_STATE register and mask out the reserved bits (bits 31:30)
    uint32_t reg_val = lsu_read_32(LC_CTRL_LC_STATE_OFFSET) & 0x3FFFFFFF;
    const char *state_str;

    // The state *should* be a repeated copy of a 5-bit value. Loop over the 32 bits (for each
    // complete 5-bit window) and extract the 5-bit value (assuming there is one). Set the "bottom
    // value" to the impossible 0xff if there is not.
    unsigned rep_val = reg_val & 0x1f;

    for (int shift = 5; shift + 4 < 32; shift += 5) {
        unsigned bottom = (reg_val >> shift) & 0x1f;
        if (bottom != rep_val) {
            rep_val = 0xff;
            break;
        }
    }

    // At this point, we will either have found the repeated value, or figured out there isn't one.
    switch (rep_val) {
        case 0x0: state_str = "RAW"; break;
        case 0x1: state_str = "TEST_UNLOCKED0"; break;
        case 0x2: state_str = "TEST_LOCKED0"; break;
        case 0x3: state_str = "TEST_UNLOCKED1"; break;
        case 0x4: state_str = "TEST_LOCKED1"; break;
        case 0x5: state_str = "TEST_UNLOCKED2"; break;
        case 0x6: state_str = "TEST_LOCKED2"; break;
        case 0x7: state_str = "TEST_UNLOCKED3"; break;
        case 0x8: state_str = "TEST_LOCKED3"; break;
        case 0x9: state_str = "TEST_UNLOCKED4"; break;
        case 0xa: state_str = "TEST_LOCKED4"; break;
        case 0xb: state_str = "TEST_UNLOCKED5"; break;
        case 0xc: state_str = "TEST_LOCKED5"; break;
        case 0xd: state_str = "TEST_UNLOCKED6"; break;
        case 0xe: state_str = "TEST_LOCKED6"; break;
        case 0xf: state_str = "TEST_UNLOCKED7"; break;
        case 0x10: state_str = "DEV"; break;
        case 0x11: state_str = "PROD"; break;
        case 0x12: state_str = "PROD_END"; break;
        case 0x13: state_str = "RMA"; break;
        case 0x14: state_str = "SCRAP"; break;
        case 0x15: state_str = "POST_TRANSITION"; break;
        case 0x16: state_str = "ESCALATE"; break;
        case 0x17: state_str = "INVALID"; break;
        default:   state_str = "UNKNOWN"; break;
    }

    VPRINTF(LOW, "LC_CTRL_LC_STATE register: 0x%08x (rep %d), Decoded state: %s\n",
            reg_val, rep_val, state_str);

    // Return decoded LC state.
    return rep_val;
}

bool check_lc_state(const char *desc, uint8_t exp_idx)
{
    uint8_t act_idx = read_lc_state();
    if (act_idx != exp_idx) {
        VPRINTF(LOW, "ERROR: Wrong lc_state. Expected %s (0x%x), but got 0x%x, from 0x%08.\n",
                desc, exp_idx, act_idx, lsu_read_32(LC_CTRL_LC_STATE_OFFSET));
        return false;
    }
    return true;
}

uint8_t read_lc_counter(void) {
    mcu_sleep(512);

    // Read LC_CTRL_LC_TRANSITION_CNT register and mask out the reserved bits (bits 31:5)
    uint32_t reg_val = lsu_read_32(LC_CTRL_LC_TRANSITION_CNT_OFFSET) & 0x1F;

    VPRINTF(LOW, "LC_CTRL_LC_TRANSITION_CNT register: 0x%08x\n", reg_val);

    return reg_val;
}

void disable_lcc_SVAs(void) {
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_DISABLE_SVA);
    VPRINTF(LOW, "MCU: LCC's SVAs are turned off!\n");
}

void enable_lcc_SVAs(void) {
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_ENABLE_SVA);
    VPRINTF(LOW, "MCU: LCC's SVAs are turned on!\n");
}
