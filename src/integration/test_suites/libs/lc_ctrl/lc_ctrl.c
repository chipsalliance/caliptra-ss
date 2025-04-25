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

uint32_t raw_unlock_token[4] = {
    0xef1fadea, 0xadfc9693, 0x421748a2, 0xf12a5911
};

void lcc_initialization(void) {

    uint32_t reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
    uint32_t loop_ctrl = ((reg_value & CALIPTRA_SS_LC_CTRL_READY_MASK)>>1); 
    while(!loop_ctrl){
        VPRINTF(LOW, "Read Register [0x%08x]: 0x%08x anded with 0x%08x \n", LC_CTRL_STATUS_OFFSET, reg_value, CALIPTRA_SS_LC_CTRL_READY_MASK); 
        reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
        loop_ctrl = ((reg_value & CALIPTRA_SS_LC_CTRL_READY_MASK)>>1); 
    }
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is ready!\n");
    reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
    loop_ctrl = (reg_value & CALIPTRA_SS_LC_CTRL_INIT_MASK); 
    while(!loop_ctrl){
        VPRINTF(LOW, "Read Register [0x%08x]: 0x%08x anded with 0x%08x \n", LC_CTRL_STATUS_OFFSET, reg_value, CALIPTRA_SS_LC_CTRL_INIT_MASK); 
        reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
        loop_ctrl = (reg_value & CALIPTRA_SS_LC_CTRL_INIT_MASK); 
    }
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is initalized!\n");
}

void force_lcc_tokens(void) {
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FORCE_LC_TOKENS);
    VPRINTF(LOW, "MCU: LCC TOKENs are forced to certain values!\n");
}

void sw_transition_req(uint32_t next_lc_state,
                        uint32_t token_31_0,
                        uint32_t token_63_32,
                        uint32_t token_95_64,
                        uint32_t token_127_96,
                        uint32_t conditional)
{
    uint32_t reg_value;
    uint32_t status_val;
    uint32_t loop_ctrl;
    int trigger_alert = 0;
    reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
    loop_ctrl = (reg_value & CALIPTRA_SS_LC_CTRL_INIT_MASK); 
    while(!loop_ctrl){
        VPRINTF(LOW, "Read Register [0x%08x]: 0x%08x anded with 0x%08x \n", LC_CTRL_STATUS_OFFSET, reg_value, CALIPTRA_SS_LC_CTRL_INIT_MASK); 
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
    if (conditional == 1) {        
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_31_0);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET, token_31_0);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_63_32);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_1_OFFSET, token_63_32);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_95_64);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_2_OFFSET, token_95_64);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_127_96);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_3_OFFSET, token_127_96);
    }

    // Step 6: Trigger the Transition Command
    VPRINTF(LOW, "Triggering transition command [0x%08x]: 0x1\n", LC_CTRL_TRANSITION_CMD_OFFSET);
    lsu_write_32(LC_CTRL_TRANSITION_CMD_OFFSET, 0x1);

    // Step 7: Poll Status Register
    VPRINTF(LOW, "Polling status register [0x%08x]...\n", LC_CTRL_STATUS_OFFSET);
    while (1) {
        status_val = lsu_read_32(LC_CTRL_STATUS_OFFSET);
        uint32_t TRANSITION_SUCCESSFUL = ((status_val & 0x8) >> 3);
        uint32_t TRANSITION_COUNT_ERROR = ((status_val & 0x10) >> 4);
        uint32_t TRANSITION_ERROR = ((status_val & 0x20) >> 5);
        uint32_t TOKEN_ERROR = ((status_val & 0x40) >> 6);
        uint32_t RMA_ERROR = ((status_val & 0x80) >> 7);
        uint32_t OTP_ERROR = ((status_val & 0x100) >> 8);
        uint32_t STATE_ERROR = ((status_val & 0x200) >> 9);
        uint32_t BUS_INTG_ERROR = ((status_val & 0x400) >> 10);
        uint32_t OTP_PARTITION_ERROR = ((status_val & 0x800) >> 11);
    

        if (TRANSITION_SUCCESSFUL) {
            VPRINTF(LOW, "Transition successful.\n");
            break;
        }
        if (TRANSITION_ERROR) {
            VPRINTF(LOW, "Transition error detected.\n");
            break;
        }
        if (TOKEN_ERROR) {
            VPRINTF(LOW, "Token error detected.\n");
            break;
        }
        if (OTP_ERROR) {
            VPRINTF(LOW, "OTP error detected.\n");
            break;
        }
        if (RMA_ERROR) {
            VPRINTF(LOW, "FLASH RMA error detected.\n");
            break;
        }
        if (TRANSITION_COUNT_ERROR) {
            VPRINTF(LOW, "Transition count error detected.\n");
            break;
        }
        if (STATE_ERROR) {
            VPRINTF(LOW, "State error detected.\n");
            break;
        }
        if (BUS_INTG_ERROR) {
            VPRINTF(LOW, "Bus integrity error detected.\n");
            break;
        }
        if (OTP_PARTITION_ERROR) {
            VPRINTF(LOW, "OTP partition error detected.\n");
            break;
        }
    }
    
    lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, 0x0);

    VPRINTF(LOW, "sw_transition_req completed.\n");
}

uint32_t calc_lc_state_mnemonic(uint32_t state) {
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

void transition_state(uint32_t next_lc_state, uint32_t token_31_0, uint32_t token_63_32, uint32_t token_95_64, uint32_t token_127_96, uint32_t conditional) {
    uint32_t next_lc_state_mne = calc_lc_state_mnemonic(next_lc_state);
    sw_transition_req(next_lc_state_mne, token_31_0, token_63_32, token_95_64, token_127_96, conditional);
    reset_fc_lcc_rtl();
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is in %d state!\n", next_lc_state);
}

void transition_state_req_with_expec_error(uint32_t next_lc_state, uint32_t token_31_0, uint32_t token_63_32, uint32_t token_95_64, uint32_t token_127_96, uint32_t conditional) {
    uint32_t next_lc_state_mne = calc_lc_state_mnemonic(next_lc_state);
    sw_transition_req_with_expec_error(next_lc_state_mne, token_31_0, token_63_32, token_95_64, token_127_96, conditional);
    reset_fc_lcc_rtl();
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is in %d state!\n", next_lc_state);
}

void transition_state_check(uint32_t next_lc_state, uint32_t token_31_0, uint32_t token_63_32, uint32_t token_95_64, uint32_t token_127_96, uint32_t conditional) {
    transition_state(next_lc_state, token_31_0, token_63_32, token_95_64, token_127_96, conditional);
    wait_dai_op_idle(0);
    uint32_t lc_state_curr = read_lc_state();
    if (lc_state_curr != next_lc_state) {
        VPRINTF(LOW, "ERROR: incorrect state: exp: %d, act %d\n", next_lc_state, lc_state_curr);
        exit(1);
    }
}

void test_all_lc_transitions_no_RMA_no_SCRAP(void) {
    
    // Example token for the Raw->TestUnlocked0 jump (128 bits).
    // Adjust to match your real raw-unlock token if needed.
    uint32_t token_value = 1;
    // We start at index0=0 (Raw). We do transitions *from* each state
    // to the *next* in the sequence. So we loop from i=0 to i=(N-2).
    int n_states = sizeof(state_sequence)/sizeof(state_sequence[0]);
    for (int i = 0; i < (n_states - 3); i++) {
        uint32_t from_state = state_sequence[i];
        uint32_t to_state   = state_sequence[i+1];
        VPRINTF(LOW, "\n=== Transition from %08d to %08d ===\n", 
                from_state, to_state);
        // Pack the 5-bit repeated code
        uint32_t next_lc_state_30 = calc_lc_state_mnemonic(to_state);
        
        if (i == 0){
             sw_transition_req(next_lc_state_30,
                            raw_unlock_token[0],
                            raw_unlock_token[1],
                            raw_unlock_token[2],
                            raw_unlock_token[3],
                              1 /*use_token*/);
            // check_lc_state(next_lc_state_30);
        }
        else if (i<15){
            // Decide whether to use a token
            if (use_token[i+1]) {
                // We’re using the  token for demonstration.
                sw_transition_req(next_lc_state_30,
                                0, 0, 0, 0,
                                1 /*use_token*/);
            } else {
                // No token is needed
                sw_transition_req(next_lc_state_30,
                                0, 0, 0, 0,
                                0 /*use_token*/);
            }
        }
        else{

            // Decide whether to use a token
            if (use_token[i+1]) {
                // We’re using the  token for demonstration.
                sw_transition_req(next_lc_state_30,
                                token_value, token_value, token_value, token_value,
                                1 /*use_token*/);
            } else {
                // No token is needed
                sw_transition_req(next_lc_state_30,
                                0, 0, 0, 0,
                                0 /*use_token*/);
            }
            token_value = token_value +1;
        }
        reset_fc_lcc_rtl();
    }

    VPRINTF(LOW, "All transitions complete.\n");
}

void sw_transition_req_with_expec_error(uint32_t next_lc_state,
        uint32_t token_31_0,
        uint32_t token_63_32,
        uint32_t token_95_64,
        uint32_t token_127_96,
        uint32_t conditional) {
    uint32_t reg_value;
    uint32_t status_val;
    uint32_t loop_ctrl;
    int trigger_alert = 0;
    reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
    loop_ctrl = (reg_value & CALIPTRA_SS_LC_CTRL_INIT_MASK); 

    while(!loop_ctrl){
    VPRINTF(LOW, "Read Register [0x%08x]: 0x%08x anded with 0x%08x \n", LC_CTRL_STATUS_OFFSET, reg_value, CALIPTRA_SS_LC_CTRL_INIT_MASK); 
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
    if (conditional == 1) {        
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_31_0);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET, token_31_0);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_63_32);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_1_OFFSET, token_63_32);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_95_64);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_2_OFFSET, token_95_64);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_127_96);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_3_OFFSET, token_127_96);
    }

    // Step 6: Trigger the Transition Command
    VPRINTF(LOW, "Triggering transition command [0x%08x]: 0x1\n", LC_CTRL_TRANSITION_CMD_OFFSET);
    lsu_write_32(LC_CTRL_TRANSITION_CMD_OFFSET, 0x1);

    for (uint16_t ii = 0; ii < 1000; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    // Step 7: Poll Status Register
    VPRINTF(LOW, "Polling status register [0x%08x]...\n", LC_CTRL_STATUS_OFFSET);
    while (1)
    {
        status_val = lsu_read_32(LC_CTRL_STATUS_OFFSET);
        uint32_t TRANSITION_SUCCESSFUL = ((status_val & 0x8) >> 3);
        uint32_t TRANSITION_COUNT_ERROR = ((status_val & 0x10) >> 4);
        uint32_t TRANSITION_ERROR = ((status_val & 0x20) >> 5);
        uint32_t TOKEN_ERROR = ((status_val & 0x40) >> 6);
        uint32_t RMA_ERROR = ((status_val & 0x80) >> 7);
        uint32_t OTP_ERROR = ((status_val & 0x100) >> 8);
        uint32_t STATE_ERROR = ((status_val & 0x200) >> 9);
        uint32_t BUS_INTG_ERROR = ((status_val & 0x400) >> 10);
        uint32_t OTP_PARTITION_ERROR = ((status_val & 0x800) >> 11);


        if (TRANSITION_SUCCESSFUL) {
            VPRINTF(LOW, "Transition successful but ERROR was expected...\n");
            VPRINTF(LOW, "Transition successful but the test should FAIL\n");
            break;
        }
        else if (TRANSITION_ERROR) {
            VPRINTF(LOW, "Expected Transition E**or detected.\n");
            break;
        }
        else if (TOKEN_ERROR) {
            VPRINTF(LOW, "Expected Token E**or detected.\n");
            break;
        }
        else if (OTP_ERROR) {
            VPRINTF(LOW, "Expected OTP E**or detected.\n");
            break;
        }
        else if (RMA_ERROR) {
            VPRINTF(LOW, "Expected RMA/RMA condition E**or detected.\n");
            break;
        }
        else if (TRANSITION_COUNT_ERROR) {
            VPRINTF(LOW, "Expected Transition Count E**or detected.\n");
            break;
        }
        else if (STATE_ERROR) {
            VPRINTF(LOW, "Expected State E**or detected.\n");
            break;
        }
        else if (BUS_INTG_ERROR) {
            VPRINTF(LOW, "Expected Bus Integrity E**or detected.\n");
            break;
        }
        else if (OTP_PARTITION_ERROR) {
            VPRINTF(LOW, "Expected OTP Partition E**or detected.\n");
            break;
        }
    }

    lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, 0x0);

    VPRINTF(LOW, "sw_transition_req completed.\n");
}

void force_PPD_pin(void) {
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_FORCE_RMA_SCRAP_PPD);
    VPRINTF(LOW, "MCU: RMA_SCRAP_PPD pin asserted high!\n");
}

uint32_t read_lc_state(void) {
    for (uint32_t i = 0; i < 512; i++) {
        __asm__ volatile ("nop");
    }
    // Read LC_CTRL_LC_STATE register and mask out the reserved bits (bits 31:30)
    uint32_t reg_val = lsu_read_32(LC_CTRL_LC_STATE_OFFSET) & 0x3FFFFFFF;
    const char *state_str;

    // Decode the redundant encoding.  (The encoding is defined as six repeated 5-bit values.)
    switch (reg_val) {
        case 0x00000000: state_str = "RAW"; break;
        case 0x02108421: state_str = "TEST_UNLOCKED0"; break;
        case 0x04210842: state_str = "TEST_LOCKED0"; break;
        case 0x06318c63: state_str = "TEST_UNLOCKED1"; break;
        case 0x08421084: state_str = "TEST_LOCKED1"; break;
        case 0x0a5294a5: state_str = "TEST_UNLOCKED2"; break;
        case 0x0c6318c6: state_str = "TEST_LOCKED2"; break;
        case 0x0e739ce7: state_str = "TEST_UNLOCKED3"; break;
        case 0x10842108: state_str = "TEST_LOCKED3"; break;
        case 0x1294a529: state_str = "TEST_UNLOCKED4"; break;
        case 0x14a5294a: state_str = "TEST_LOCKED4"; break;
        case 0x16b5ad6b: state_str = "TEST_UNLOCKED5"; break;
        case 0x18c6318c: state_str = "TEST_LOCKED5"; break;
        case 0x1ad6b5ad: state_str = "TEST_UNLOCKED6"; break;
        case 0x1ce739ce: state_str = "TEST_LOCKED6"; break;
        case 0x1ef7bdef: state_str = "TEST_UNLOCKED7"; break;
        case 0x21084210: state_str = "DEV"; break;
        case 0x2318c631: state_str = "PROD"; break;
        case 0x25294a52: state_str = "PROD_END"; break;
        case 0x2739ce73: state_str = "RMA"; break;
        case 0x294a5294: state_str = "SCRAP"; break;
        case 0x2b5ad6b5: state_str = "POST_TRANSITION"; break;
        case 0x2d6b5ad6: state_str = "ESCALATE"; break;
        case 0x2f7bdef7: state_str = "INVALID"; break;
        default:         state_str = "UNKNOWN"; break;
    }

    VPRINTF(LOW, "LC_CTRL_LC_STATE register: 0x%08x, Decoded state: %s\n", reg_val, state_str);

    // Return decoded LC state.
    return reg_val & 0x1F;
}

uint32_t read_lc_counter(void) {
    for (uint32_t i = 0; i < 512; i++) {
        __asm__ volatile ("nop");
    }
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
