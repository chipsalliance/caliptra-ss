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
#include <stdbool.h>

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

// Trigger a trans_cnt_oflw_error in the lc_ctrl FSM.
void trans_cnt_oflw_error(void) {
    // Fault the lc counter fuse to trigger a overflow error.
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_FAULT_CNTR);
    sw_transition_req_with_expec_error(calc_lc_state_mnemonic(TEST_LOCKED0), 0, 0, 0, 0, 0);

    uint32_t status = lsu_read_32(SOC_LC_CTRL_STATUS);
    if (!((status  >> LC_CTRL_STATUS_TRANSITION_COUNT_ERROR_LOW) & 0x1)) {
        VPRINTF(LOW, "ERROR: lc transition count error is not signaled\n");
    }
}

// Trigger a trans_invalid_error in the lc_ctrl FSM.
void trans_invalid_error(void) {
    // Reverting back to the RAW state from TEST_UNLOCKED0 is not allowed.
    sw_transition_req_with_expec_error(calc_lc_state_mnemonic(RAW), 0, 0, 0, 0, 0);

    uint32_t status = lsu_read_32(SOC_LC_CTRL_STATUS);
    if (!((status  >> LC_CTRL_STATUS_TRANSITION_ERROR_LOW) & 0x1)) {
        VPRINTF(LOW, "ERROR: lc transition error is not signaled\n");
    }
}

// Trigger a token_invalid_error in the lc_ctrl FSM.
void token_invalid_error(void) {
    // Transitioning from TEST_LOCKED0 to TEST_UNLOCKED1 needs a correct token.
    sw_transition_req(calc_lc_state_mnemonic(TEST_LOCKED0), 0, 0, 0, 0, 0);
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);
    sw_transition_req_with_expec_error(calc_lc_state_mnemonic(TEST_UNLOCKED1), 0, 0, 0, 0, 1);

    uint32_t status = lsu_read_32(SOC_LC_CTRL_STATUS);
    if (!((status  >> LC_CTRL_STATUS_TOKEN_ERROR_LOW) & 0x1)) {
        VPRINTF(LOW, "ERROR: lc token error is not signaled\n");
    }
}

// Trigger a flash_rma_error in the lc_ctrl FSM.
void flash_rma_error(void) {
    // Transitioning into the RMA state without forcing PPD pin will result in a flash_rma_error.
    sw_transition_req_with_expec_error(calc_lc_state_mnemonic(RMA), 0, 0, 0, 0, 0);

    uint32_t status = lsu_read_32(SOC_LC_CTRL_STATUS);
    if (!((status  >> LC_CTRL_STATUS_FLASH_RMA_ERROR_LOW) & 0x1)) {
        VPRINTF(LOW, "ERROR: lc flash rma is not signaled %08X\n", status);
    }
}

// Trigger a otp_prog_error in the lc_ctrl FSM.
void otp_prog_error(void) {
    // Activating a clk bypass without acknowledging the request will result in ann opt_prog_error.
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_DISABLE_CLK_BYP_ACK);
    lsu_write_32(LC_CTRL_TRANSITION_CTRL_OFFSET, 0x1);
    sw_transition_req(calc_lc_state_mnemonic(TEST_LOCKED0), 0, 0, 0, 0, 0);

    uint32_t status = lsu_read_32(SOC_LC_CTRL_STATUS);
    if (!((status  >> LC_CTRL_STATUS_OTP_ERROR_LOW) & 0x1)) {
        VPRINTF(LOW, "ERROR: lc otp error is not signaled %08X\n", status);
    }
}

// Trigger a state_invalid_error in the lc_ctrl FSM.
void state_invalid_error(void) {
    // Transitioning into the SCRAP state without forcing the PPD pin will result in a state_invalid_error.
    sw_transition_req_with_expec_error(calc_lc_state_mnemonic(SCRAP), 0, 0, 0, 0, 0);

    uint32_t status = lsu_read_32(SOC_LC_CTRL_STATUS);
    if (!((status  >> LC_CTRL_STATUS_STATE_ERROR_LOW) & 0x1)) {
        VPRINTF(LOW, "ERROR: lc state error is not signaled %08X\n", status);
    }
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    transition_state_check(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);

    initialize_otp_controller();

    switch (xorshift32() % 6) {
        case 0: {
            VPRINTF(LOW, "INFO: triggering trans_cnt_oflw_error\n");
            trans_cnt_oflw_error();
            break;
        }
        case 1: {
            VPRINTF(LOW, "INFO: triggering trans_invalid_error\n");
            trans_invalid_error();
            break;
        }
        case 2: {
            VPRINTF(LOW, "INFO: triggering token_invalid_error\n");
            token_invalid_error();
            break;
        }
        case 3: {
            VPRINTF(LOW, "INFO: triggering flash_rma_error\n");
            flash_rma_error();
            break;
        }
        case 4: {
            VPRINTF(LOW, "INFO: triggering otp_prog_error\n");
            otp_prog_error();
            break;
        }
        default: {
            VPRINTF(LOW, "INFO: triggering state_invalid_error\n");
            state_invalid_error();
            break;
        }
    }

epilogue:
    for (uint8_t i = 0; i < 160; i++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
