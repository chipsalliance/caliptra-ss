//********************************************************************************
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
//********************************************************************************

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "fuse_ctrl_address_map.h"
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



void main (void)
{
    VPRINTF(LOW, "=================\nMCU: Caliptra Boot Go\n=================\n\n");    
    mcu_cptra_init_d(.cfg_skip_set_fuse_done=true);

    uint32_t lc_state_curr = read_lc_state();
    uint32_t lc_cnt_curr = read_lc_counter();
    if (lc_state_curr == 19) {
        // Transition to SCRAP require setting the PPD pin.
        force_PPD_pin();
    }
    for (uint16_t ii = 0; ii < 100; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    VPRINTF(LOW, "=================\n CALIPTRA_SS JTAG TEST with ROM \n=================\n\n");

    if (lc_state_curr == 18 || lc_state_curr == 20 || lc_cnt_curr == 24 ) {
        for (uint16_t ii = 0; ii < 10000; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
        SEND_STDOUT_CTRL(0xff);
    }
    else {    
        uint32_t next_lc_state = read_lc_state();
        while (next_lc_state != 21) {
            VPRINTF(LOW, "\nMCU: CALIPTRA_SS_LC_CTRL is in %d state!\n", next_lc_state);
            VPRINTF(LOW, "\nMCU: CALIPTRA_SS_LC_CTRL is not in POST_TRANS state!\n");
            next_lc_state = read_lc_state();
            for (uint16_t ii = 0; ii < 100; ii++) {
                __asm__ volatile ("nop"); // Sleep loop as "nop"
            }
        }
        reset_fc_lcc_rtl();
        wait_dai_op_idle(0);
        next_lc_state = read_lc_state();
        if ((lc_state_curr+1) != next_lc_state) {
            VPRINTF(LOW, "ERROR: incorrect state: exp: %d, act %d\n", next_lc_state, lc_state_curr);
            exit(1);
        }

        SEND_STDOUT_CTRL(0xff);
    }

}
