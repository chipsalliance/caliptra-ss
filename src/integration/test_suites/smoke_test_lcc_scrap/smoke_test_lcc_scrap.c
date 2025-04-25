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


void from_Unlocked_to_SCRAP(void) {

    uint32_t reg_value;    
    uint32_t from_state;
    uint32_t to_state;   

    from_state = 1;
    to_state   = 20;
    VPRINTF(LOW, "\n=== Transition from %08d to %08d ===\n", 
        from_state, to_state);
    // Pack the 5-bit repeated code
    uint32_t next_lc_state_30 = calc_lc_state_mnemonic(to_state);
    force_PPD_pin();
    sw_transition_req(next_lc_state_30,
                                0, 0, 0, 0,
                                0 /*use_token*/);
    reset_fc_lcc_rtl();
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is in SCRAP state!\n");

}

void no_PPD_from_Raw_to_SCRAP(void) {

    disable_lcc_SVAs();
    uint32_t reg_value;
    uint32_t from_state = 0;
    uint32_t to_state   = 1;
    VPRINTF(LOW, "\n=== Transition from 0x%08x to 0x%08x ===\n", 
            from_state, to_state);
    uint32_t next_lc_state_30 = calc_lc_state_mnemonic(to_state);

    sw_transition_req(next_lc_state_30,
                        raw_unlock_token[0],
                        raw_unlock_token[1],
                        raw_unlock_token[2],
                        raw_unlock_token[3],
                        1 /*use_token*/);
    
    reset_fc_lcc_rtl();
    from_state = 1;
    to_state   = 20;
    VPRINTF(LOW, "\n=== Transition from 0x%08x to 0x%08x ===\n", 
            from_state, to_state);
    // Pack the 5-bit repeated code
    next_lc_state_30 = calc_lc_state_mnemonic(to_state);   
    sw_transition_req_with_expec_error(next_lc_state_30,
                                0, 0, 0, 0,
                                0 /*use_token*/);
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is in not SCRAP state!\n");
    reset_fc_lcc_rtl();
    enable_lcc_SVAs();
   
}

void main (void)
{
    VPRINTF(LOW, "=================\nMCU: Caliptra Boot Go\n=================\n\n");    
    mcu_cptra_init_d(.cfg_skip_set_fuse_done=true);
    force_lcc_tokens();
    VPRINTF(LOW, "=========\nMCU: TESTING LCC STATE TRANS FROM ONE to SCRAP\n=================\n\n");   
    no_PPD_from_Raw_to_SCRAP();
    from_Unlocked_to_SCRAP(); 
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    SEND_STDOUT_CTRL(0xff);

}
