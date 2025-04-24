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

void wait_dai_op_idle_no_mask() {
    uint32_t status;
    uint32_t dai_idle;
    uint32_t check_pending;
    VPRINTF(LOW, "DEBUG: Waiting for DAI to become idle...\n");
    do {
        status = lsu_read_32(SOC_OTP_CTRL_STATUS);
        dai_idle = (status >> OTP_CTRL_STATUS_DAI_IDLE_LOW) & 0x1;
        check_pending = (status >> OTP_CTRL_STATUS_CHECK_PENDING_LOW) & 0x1;
    } while ((!dai_idle || check_pending) && ((status & 0x3FFFF) != 0x3FFFF));

    VPRINTF(LOW, "DEBUG: DAI is now idle.\n");
    return;
}

void main (void)
{
    VPRINTF(LOW, "=================\nMCU: Caliptra Boot Go\n=================\n\n");    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    for (uint16_t ii = 0; ii < 100; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    VPRINTF(LOW, "=================\n CALIPTRA_SS JTAG TEST with ROM \n=================\n\n");

    // Permanently force the PPD pin. This is needed as it seems
    // that we cannot force the PPD pin from the JTAG TCL script.
    force_PPD_pin();

    // The JTAG TCL script will trigger state transitions in parallel.
    // This loop waits until we've received TRANSITION_SUCCESSFUL.
    // Once received, trigger a FCC_LCC reset such that the state
    // transition can be finished and the next state transition can
    // happen. Once we've received the final SCRAP state, exit the
    // test.
    while(1) {
        for (uint16_t ii = 0; ii < 600; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }

        uint32_t lc_state_curr = read_lc_state();
        if (lc_state_curr == SCRAP) {
            VPRINTF(LOW, "Reached the final state, exit test.\n"); 
            break;
        }

        uint32_t lc_cntn_curr = read_lc_counter();
        if (lc_cntn_curr == 24) {
            VPRINTF(LOW, "Reached the final counter, exit test.\n"); 
            break;
        }

        // Claim mutex.
        uint32_t loop_ctrl = 0;
        while (loop_ctrl != CLAIM_TRANS_VAL) {
            lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, CLAIM_TRANS_VAL);
            uint32_t reg_value = lsu_read_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET);
            loop_ctrl = reg_value & CLAIM_TRANS_VAL;
        }

        // Read status value.
        uint32_t status_val = lsu_read_32(LC_CTRL_STATUS_OFFSET);
        uint32_t TRANSITION_SUCCESSFUL = ((status_val & 0x8) >> 3);

        // Release status value.
        lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, 0x0);

        // If we had a successful transition, trigger reset.
        if (TRANSITION_SUCCESSFUL) {
            reset_fc_lcc_rtl();
            wait_dai_op_idle_no_mask();
        }
    }
   SEND_STDOUT_CTRL(0xff);
}
