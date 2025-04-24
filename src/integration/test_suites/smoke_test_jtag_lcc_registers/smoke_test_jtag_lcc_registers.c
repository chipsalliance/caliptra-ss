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

#define CLAIM_TRANS_VAL 0x96 // Tried to match MuBi8True

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

    VPRINTF(LOW, "=================\n CALIPTRA_SS JTAG TEST with ROM \n=================\n\n");

    for (uint16_t ii = 0; ii < 6000; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    uint32_t finish_flag = lsu_read_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET);
    VPRINTF(LOW, "MCU: waits in loop until JTAG done!\n");
    while(finish_flag != 0xABCDEFCA){
        // Claim the TRANSITION_IF mutex.
        uint32_t loop_ctrl = 0;
        while (loop_ctrl != 0x96) {
            lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, CLAIM_TRANS_VAL);
            uint32_t reg_value = lsu_read_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET);
            loop_ctrl = reg_value & 0xff;
        }

        // Read the flag.
        finish_flag = lsu_read_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET);

        // Release the TRANSITION_IF mutex.
        lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, 0x0);

        // Wait a bit before trying again.
        for (uint32_t ii = 0; ii < 500; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    }

    SEND_STDOUT_CTRL(0xff);

}
