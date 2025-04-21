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
// ## LCC Escalation Test
// 
// This test initializes randomly the FC VMEM file and sets a random LC starting
// state as well as LC counter. Then, randomly either raise the esc_scrap_state0
// or esc_scrap_state1 port. Check, if we are in the ESCALATE LC state. Then
// try a state transition to starting state + 1. This should fail and we still
// should be in the ESCALATE LC state.
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl_address_map.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"

#define CLAIM_TRANS_VAL 0x96 // Tried to match MuBi8True

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

static uint32_t tokens[13][4] = {
    [RAU] = {0xef1fadea, 0xadfc9693, 0x421748a2, 0xf12a5911}, // RAW_UNLOCK
    [TU1] = {0x72f04808, 0x05f493b4, 0x7790628a, 0x318372c8}, // TEST_UNLOCKED1
    [TU2] = {0x17c78a78, 0xc7b443ef, 0xd6931045, 0x55e74f3c}, // TEST_UNLOCKED2
    [TU3] = {0x1644aa12, 0x79925802, 0xdbc26815, 0x8597a5fa}, // TEST_UNLOCKED3
    [TU4] = {0x34d1ea6e, 0x121f023f, 0x6e9dc51c, 0xc7439b6f}, // TEST_UNLOCKED4
    [TU5] = {0x03fd9df1, 0x20978af4, 0x49db216d, 0xb0225ece}, // TEST_UNLOCKED5
    [TU6] = {0xcfc0871c, 0xc400e922, 0x4290a4ad, 0x7f10dc89}, // TEST_UNLOCKED6
    [TU7] = {0x67e87f3e, 0xae6ee167, 0x802efa05, 0xbaaa3138}, // TEST_UNLOCKED7
    [TEX] = {0x2f533ae9, 0x341d2478, 0x5f066362, 0xb5fe1577}, // TEST_EXIT
    [DEX] = {0xf622abb6, 0x5d8318f4, 0xc721179d, 0x51c001f2}, // DEV_EXIT
    [PEX] = {0x25b8649d, 0xe7818e5b, 0x826d5ba4, 0xd6b633a0}, // PROD_EXIT
    [RMU] = {0x72f04808, 0x05f493b4, 0x7790628a, 0x318372c8}, // RMA
    [ZER] = {0}                                               // ZERO
};

void trigger_zeroize() {
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FC_FORCE_ZEROIZATION);
    for (uint8_t i = 0; i < 160; i++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
}

void sw_transition_req_with_zeroize(uint32_t next_lc_state,
                                    uint32_t token_31_0,
                                    uint32_t token_63_32,
                                    uint32_t token_95_64,
                                    uint32_t token_127_96,
                                    uint32_t conditional,
                                    uint32_t zeroize_pos)
{
    // Trigger zeroize before the state transition.
    if (zeroize_pos == 0) {
        trigger_zeroize();
    }
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
    // Trigger zeroize before claiming the transition register.
    if (zeroize_pos == 1) {
        trigger_zeroize();
    }
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
    // Trigger zeroize before setting the next lifecycle state.
    if (zeroize_pos == 2) {
        trigger_zeroize();
    }
    VPRINTF(LOW, "Setting next lifecycle state [0x%08x]: 0x%08x\n", LC_CTRL_TRANSITION_TARGET_OFFSET, next_lc_state);
    lsu_write_32(LC_CTRL_TRANSITION_TARGET_OFFSET, next_lc_state);

    // Step 4: Write Transition Tokens
    // Trigger zeroize before writing the transition tokens.
    if (zeroize_pos == 3) {
        trigger_zeroize();
    }
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
    // Trigger zeroize before triggering the transition command.
    if (zeroize_pos == 4) {
        trigger_zeroize();
    }
    VPRINTF(LOW, "Triggering transition command [0x%08x]: 0x1\n", LC_CTRL_TRANSITION_CMD_OFFSET);
    lsu_write_32(LC_CTRL_TRANSITION_CMD_OFFSET, 0x1);

    // Step 7: Poll Status Register
    // Trigger zeroize before polling the status register.
    if (zeroize_pos == 5) {
        trigger_zeroize();
    }
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

    // Trigger zeroize before releasing the mutex.
    if (zeroize_pos == 6) {
        trigger_zeroize();
    }
    lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, 0x0);

    // Trigger zeroize after the state transition.
    if (zeroize_pos == 7) {
        trigger_zeroize();
    }

    VPRINTF(LOW, "sw_transition_req completed.\n");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")

    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    uint32_t buf[NUM_LC_STATES] = {0};

    // Randomly choose the next LC state among the all valid ones
    // based on the current state.
    lcc_initialization();

    // Get current state and counter value.
    uint32_t lc_state_curr = read_lc_state();
    uint32_t lc_cnt_curr = read_lc_counter();
    uint32_t lc_cnt_next = lc_cnt_curr + 1;
    VPRINTF(LOW, "INFO: current lcc state: %d\n", lc_state_curr);
    VPRINTF(LOW, "INFO: current lc cntc state: %d\n", lc_cnt_curr);

    if (lc_cnt_curr == 24) {
        VPRINTF(LOW, "INFO: reached the lc_cntc limit of 24, finish test.\n");
        for (uint8_t i = 0; i < 160; i++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
        SEND_STDOUT_CTRL(0xff);
    }

    // Get the valid state transitions from the current state.
    uint32_t count = 0;
    memset(buf, 0, sizeof(buf));
    for (uint32_t i = 1, k = 0; (i + lc_state_curr)< NUM_LC_STATES; i++) {
        if (trans_matrix[lc_state_curr][i+lc_state_curr] != INV) {
            buf[count] = i + lc_state_curr;
            count++;
        }
    }

    if (count == 0) {
        VPRINTF(LOW, "INFO: could not fine a next state based on the transition matrix, finish test.\n");
        for (uint8_t i = 0; i < 160; i++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
        SEND_STDOUT_CTRL(0xff);
    } else {
        // Select a random next state.
        uint32_t lc_state_next = buf[xorshift32() % count];
        VPRINTF(LOW, "INFO: next lcc state: %d\n", lc_state_next);

        // Force PPD pin if target state is SCRAP or RMA.
        if (lc_state_next == SCRAP || lc_state_next == RMA) {
            force_PPD_pin();
        }

        // Check if we need a transition unlock token.
        lc_token_type_t token_type = trans_matrix[lc_state_curr][lc_state_next];

        // Determine at which position we are triggering the zeroize command.
        // Either before, during, or after the state transition.
        uint32_t zeroize_pos = xorshift32() % 8;

        // Trigger state transition.
        uint32_t next_lc_state_mne = calc_lc_state_mnemonic(lc_state_next);
        sw_transition_req_with_zeroize(next_lc_state_mne,
                                       tokens[token_type][0],
                                       tokens[token_type][1],
                                       tokens[token_type][2],
                                       tokens[token_type][3],
                                       token_type != ZER,
                                       zeroize_pos);
        reset_fc_lcc_rtl();
        wait_dai_op_idle(0);

        lc_state_curr = read_lc_state();
        VPRINTF(LOW, "Info: now in state: %d\n", lc_state_curr);
        lc_state_curr = read_lc_state();

        // TODO: check if we got expected behavior.
    }

    SEND_STDOUT_CTRL(0xff);
}
