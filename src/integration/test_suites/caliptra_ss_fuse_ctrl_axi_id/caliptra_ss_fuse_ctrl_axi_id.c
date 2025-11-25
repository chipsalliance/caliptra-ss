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

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"
#include "fuse_ctrl_mmap.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

/**
 * This test performs DAI writes over the AXI bus on the boundaries of the
 * fuse controller access table entries with randomized fuse writes and
 * random AXI user ids.
 */
bool axi_id() {
    const uint32_t sentinel = 0xAB;

    for (int i = 0; i < 4; i++) {
        // Exclude life-cycle partition as it is not writable.
        partition_t partition = partitions[xorshift32() % (NUM_PARTITIONS-1)];
        bool axi_user = xorshift32() % 2;
        
        if (axi_user) {
            grant_mcu_for_fc_writes();
        } else {
            grant_caliptra_core_for_fc_writes();
        }

        // There are some secret partitions that can't be modified with an AXI request from the MCU.
        // If this is a partition, we expect the DAI transaction to end with a status of DAI_ERROR.
        uint32_t exp_status = ((is_caliptra_secret_addr(partition.address) && axi_user) ?
                               OTP_CTRL_STATUS_DAI_ERROR_MASK :
                               0);
        if (!dai_wr(partition.address, sentinel, sentinel, partition.granularity, exp_status))
            return false;
    }

    return true;
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    transition_state_check(TEST_UNLOCKED0, raw_unlock_token);

    initialize_otp_controller();

    axi_id();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
