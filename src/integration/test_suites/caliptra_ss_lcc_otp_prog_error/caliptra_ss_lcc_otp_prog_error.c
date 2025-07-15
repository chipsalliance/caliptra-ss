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

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    uint32_t buf[NUM_LC_STATES] = {0};

    // Randomly choose the next LC state among the all valid ones
    // based on the current state and repeat this until the SCRAP
    // state is reached.
    while (1) {
        lcc_initialization();
        force_PPD_pin();

        uint32_t lc_state_curr = read_lc_state();
        uint32_t lc_cnt_curr = read_lc_counter();
        uint32_t lc_cnt_next = lc_cnt_curr + 1; 

        VPRINTF(LOW, "INFO: current lcc state: %d\n", lc_state_curr);
        VPRINTF(LOW, "INFO: current lc cntc state: %d\n", lc_cnt_curr);

        uint32_t count = 0;
        memset(buf, 0, sizeof(buf));
        for (uint32_t i = 1, k = 0; (i + lc_state_curr)< NUM_LC_STATES; i++) {
            if (trans_matrix[lc_state_curr][i+lc_state_curr] != INV) {
                buf[count] = i + lc_state_curr;
                count++;
            }
        }

        if (count) {
            uint32_t lc_state_next = buf[xorshift32() % count];
            VPRINTF(LOW, "INFO: next lcc state: %d\n", lc_state_next);

            lc_token_type_t token_type = trans_matrix[lc_state_curr][lc_state_next];
            // Activating a clk bypass without acknowledging the request will result in ann opt_prog_error.
            lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_DISABLE_CLK_BYP_ACK);
            // We should see: OTP E**or detected.
            transition_state_req_with_expec_error(lc_state_next,
                         tokens[token_type][0],
                         tokens[token_type][1],
                         tokens[token_type][2],
                         tokens[token_type][3],
                         token_type != ZER);
            goto epilogue;
        }
    }
    
epilogue:
    for (uint8_t i = 0; i < 160; i++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
