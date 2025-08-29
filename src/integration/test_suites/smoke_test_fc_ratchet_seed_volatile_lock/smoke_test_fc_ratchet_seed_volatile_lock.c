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
   This tests sets the ratchet_seed_volatile_lock increasingly from all its possible value and checks which partitions are writable 
 */

// Tests the volatile lock by setting it to every possible value and writing/reading to each ratchet seed register

void ratchet_seed_volatile_lock(void) {
    uint32_t data[2];

    VPRINTF(LOW, "==================================\n testing all ratchet seed registers: \n")
    VPRINTF(LOW, "testing all ratchet seed registers. ratcher_seed_volatile_lock = 0 \n==================================\n\n")
    // LOCK set to 0x0 - all partitions are writable
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_0].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_1].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_2].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_3].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_4].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_5].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_6].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_7].address, 0xFF, 0xFF, 32, 0);

    // LOCK set to 0x1 - only partition 0 is not writable
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0x1);
    VPRINTF(LOW, "==================================\n testing all ratchet seed registers: \n")
    VPRINTF(LOW, "testing all ratchet seed registers. ratcher_seed_volatile_lock = 1 \n==================================\n\n")
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_0].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_1].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_2].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_3].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_4].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_5].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_6].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_7].address, 0xFF, 0xFF, 32, 0);

    // LOCK set to 0x2 - only partition 0,1 is not writable
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0x2);
    VPRINTF(LOW, "==================================\n testing all ratchet seed registers: \n")
    VPRINTF(LOW, "testing all ratchet seed registers. ratcher_seed_volatile_lock = 2 \n==================================\n\n")
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_0].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_1].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_2].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_3].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_4].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_5].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_6].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_7].address, 0xFF, 0xFF, 32, 0);

    // LOCK set to 0x3 - only partition 0,1,2 is not writable
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0x3);
    VPRINTF(LOW, "==================================\n testing all ratchet seed registers: \n")
    VPRINTF(LOW, "testing all ratchet seed registers. ratcher_seed_volatile_lock = 3 \n==================================\n\n")
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_0].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_1].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_2].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_3].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_4].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_5].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_6].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_7].address, 0xFF, 0xFF, 32, 0);

    // LOCK set to 0x4 - only partition 0,1,2,3 is not writable
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0x4);
    VPRINTF(LOW, "==================================\n testing all ratchet seed registers: \n")
    VPRINTF(LOW, "testing all ratchet seed registers. ratcher_seed_volatile_lock = 4 \n==================================\n\n")
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_0].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_1].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_2].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_3].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_4].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_5].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_6].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_7].address, 0xFF, 0xFF, 32, 0);

    // LOCK set to 0x5 - only partition 0,1,2,3,4 is not writable
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0x5);
    VPRINTF(LOW, "==================================\n testing all ratchet seed registers: \n")
    VPRINTF(LOW, "testing all ratchet seed registers. ratcher_seed_volatile_lock = 5 \n==================================\n\n")
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_0].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_1].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_2].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_3].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_4].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_5].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_6].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_7].address, 0xFF, 0xFF, 32, 0);

    // LOCK set to 0x6 - only partition 0,1,2,3,4,5 is not writable
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0x6);
    VPRINTF(LOW, "==================================\n testing all ratchet seed registers: \n")
    VPRINTF(LOW, "testing all ratchet seed registers. ratcher_seed_volatile_lock = 6 \n==================================\n\n")
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_0].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_1].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_2].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_3].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_4].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_5].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_6].address, 0xFF, 0xFF, 32, 0);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_7].address, 0xFF, 0xFF, 32, 0);

    // LOCK set to 0x7 - only partition 0,1,2,3,4,5,6 is not writable
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0x7);
    VPRINTF(LOW, "==================================\n testing all ratchet seed registers: \n")
    VPRINTF(LOW, "testing all ratchet seed registers. ratcher_seed_volatile_lock = 7 \n==================================\n\n")
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_0].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_1].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_2].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_3].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_4].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_5].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_6].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_7].address, 0xFF, 0xFF, 32, 0);

    // LOCK set to 0x8 - only partition 0,1,2,3,4,5,6,7 is not writable
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0x8);
    VPRINTF(LOW, "==================================\n testing all ratchet seed registers: \n")
    VPRINTF(LOW, "testing all ratchet seed registers. ratcher_seed_volatile_lock = 8 \n==================================\n\n")
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_0].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_1].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_2].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_3].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_4].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_5].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_6].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_7].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);


    VPRINTF(LOW, "Ratchet seed volatile test finished\n");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    initialize_otp_controller();

    VPRINTF(LOW, "=================\nBefore ratchet_seed_volatile_lock\n=================\n\n")
    ratchet_seed_volatile_lock();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
