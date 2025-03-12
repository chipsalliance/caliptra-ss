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

#define CLAIM_TRANS_VAL 0x96 // Tried to match MuBi8True

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

void sw_transition_req(uint32_t next_lc_state,
                        uint32_t token_127_96,
                        uint32_t token_95_64,
                        uint32_t token_63_32,
                        uint32_t token_31_0,
                        uint32_t conditional) {
    uint32_t reg_value;
    uint32_t status_val;
    uint32_t loop_ctrl;
    int trigger_alert = 0;

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
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_127_96);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET, token_127_96);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_95_64);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET, token_95_64);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_63_32);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET, token_63_32);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_31_0);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET, token_31_0);
    }

    // Step 6: Trigger the Transition Command
    VPRINTF(LOW, "Triggering transition command [0x%08x]: 0x1\n", LC_CTRL_TRANSITION_CMD_OFFSET);
    lsu_write_32(LC_CTRL_TRANSITION_CMD_OFFSET, 0x1);

    // Step 7: Poll Status Register
    VPRINTF(LOW, "Polling status register [0x%08x]...\n", LC_CTRL_STATUS_OFFSET);
    while (1) {
        status_val = lsu_read_32(LC_CTRL_STATUS_OFFSET);
        uint32_t TRANSITION_SUCCESSFUL = ((status_val & 0x8) >> 3);
        uint32_t TOKEN_ERROR = ((status_val & 0x40) >> 6);
        uint32_t OTP_ERROR = ((status_val & 0x100) >> 8);
        uint32_t RMA_ERROR = ((status_val & 0x80) >> 7);

        VPRINTF(LOW, "Status Register: 0x%08x | Transition Successful: %d | Token Error: %d | OTP Error: %d\n",
                status_val, TRANSITION_SUCCESSFUL, TOKEN_ERROR, OTP_ERROR);

        if (TRANSITION_SUCCESSFUL) {
            VPRINTF(LOW, "Transition successful.\n");
            break;
        }
        if (TOKEN_ERROR) {
            VPRINTF(LOW, "Token rror detected.\n");
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
    }
    lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, 0x0);

    VPRINTF(LOW, "sw_transition_req completed.\n");
}