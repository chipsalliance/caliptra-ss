// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
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
#include "printf.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "riscv_hw_if.h"
#include "lc_ctrl.h"

#define CLAIM_TRANS_VAL 0x96 // Tried to match MuBi8True

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
    0  // from PROD -> SCRAP
};

uint32_t raw_unlock_token[4] = {
    0xef1fadea, 0xadfc9693, 0x421748a2, 0xf12a5911
};

void lcc_initialization(void) {
    while(!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK));

    // Initialize fuses
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_FUSE_WR_DONE, SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
    VPRINTF(LOW, "MCU: Set fuse wr done\n");
    uint32_t reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
    uint32_t loop_ctrl = reg_value & CALIPTRA_SS_LC_CTRL_READY_MASK; 
    while(!loop_ctrl){
        VPRINTF(LOW, "Read Register [0x%08x]: 0x%08x anded with 0x%08x \n", LC_CTRL_STATUS_OFFSET, reg_value, CALIPTRA_SS_LC_CTRL_READY_MASK); 
        reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
        loop_ctrl = reg_value & CALIPTRA_SS_LC_CTRL_READY_MASK; 
    }
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is ready!\n");
    reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
    loop_ctrl = ((reg_value & CALIPTRA_SS_LC_CTRL_INIT_MASK)>>1) & 1; 
    while(!loop_ctrl){
        VPRINTF(LOW, "Read Register [0x%08x]: 0x%08x anded with 0x%08x \n", LC_CTRL_STATUS_OFFSET, reg_value, CALIPTRA_SS_LC_CTRL_INIT_MASK); 
        reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
        loop_ctrl = ((reg_value & CALIPTRA_SS_LC_CTRL_INIT_MASK)>>1) & 1; 
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
    loop_ctrl = ((reg_value & CALIPTRA_SS_LC_CTRL_INIT_MASK)>>1) & 1; 
    while(!loop_ctrl){
        VPRINTF(LOW, "Read Register [0x%08x]: 0x%08x anded with 0x%08x \n", LC_CTRL_STATUS_OFFSET, reg_value, CALIPTRA_SS_LC_CTRL_INIT_MASK); 
        reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
        loop_ctrl = ((reg_value & CALIPTRA_SS_LC_CTRL_INIT_MASK)>>1) & 1; 
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


void test_all_lc_transitions_no_RMA_no_SCRAP(void) {
    
    // Example token for the Raw->TestUnlocked0 jump (128 bits).
    // Adjust to match your real raw-unlock token if needed.
    uint32_t token_value = 1;
    // We start at index0=0 (Raw). We do transitions *from* each state
    // to the *next* in the sequence. So we loop from i=0 to i=(N-2).
    int n_states = sizeof(state_sequence)/sizeof(state_sequence[0]);
    for (int i = 0; i < (n_states - 2); i++) {
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
    loop_ctrl = ((reg_value & CALIPTRA_SS_LC_CTRL_INIT_MASK)>>1) & 1; 

    while(!loop_ctrl){
    VPRINTF(LOW, "Read Register [0x%08x]: 0x%08x anded with 0x%08x \n", LC_CTRL_STATUS_OFFSET, reg_value, CALIPTRA_SS_LC_CTRL_INIT_MASK); 
        reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
        loop_ctrl = ((reg_value & CALIPTRA_SS_LC_CTRL_INIT_MASK)>>1) & 1; 
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