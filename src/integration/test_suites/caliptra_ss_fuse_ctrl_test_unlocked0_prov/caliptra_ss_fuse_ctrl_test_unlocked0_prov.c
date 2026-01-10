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
#include "fuse_ctrl_mmap.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void test_unlocked0_provision() {
    const uint32_t sentinel = 0xA5;

    if (!check_lc_state("TEST_UNLOCKED0", TEST_UNLOCKED0)){
        handle_error("ERROR: Incorrect LC state at start of test_unlocked0_provision\n");
        return;
    }
    else {
        VPRINTF(LOW, "INFO: Correct LC state at start of test_unlocked0_provision\n");
    }

    uint32_t read_value, zero;
    uint32_t rnd_fuse_addresses[NUM_PARTITIONS-2]; // Exclude the last partition which is lifecycle
    VPRINTF(LOW, "INFO:: starting the task.\n");
    for (uint32_t i = 0; i < (NUM_PARTITIONS-2); i++) {
        
        if (is_caliptra_secret_addr(partitions[i].address)) {
            VPRINTF(LOW, "INFO:: Got the secret partition with index %d and address 0x%x\n", i, partitions[i].address);
            VPRINTF(LOW, "INFO:: Skipping provisioning of secret partition in debug mode.\n");
            continue; // You cannot provision secret fuses in debug mode
        }

        rnd_fuse_addresses[i] = partitions[i].fuses[xorshift32() % partitions[i].num_fuses];
        VPRINTF(LOW, "INFO:: Chosen fuse address 0x%x from partition index %d, number of fuse is %d\n", rnd_fuse_addresses[i], i, partitions[i].num_fuses);
        
        dai_wr(rnd_fuse_addresses[i], sentinel, 0, partitions[i].granularity, 0);
        
        dai_rd(rnd_fuse_addresses[i], &read_value, &zero, partitions[i].granularity, 0);
        if ((read_value & 0xFF) != sentinel) {
            VPRINTF(LOW, "ERROR: incorrect value: exp: %08X act: %08X\n", read_value, sentinel);
        }

        if (partitions[i].sw_digest) {
            dai_wr(partitions[i].digest_address, sentinel, 0, 64, 0);
        } else if (partitions[i].hw_digest) {
            calculate_digest(partitions[i].address, 0);
        }
    } 
    wait_dai_op_idle(0);
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    for (uint32_t i = 0; i < (NUM_PARTITIONS-2); i++) {
        if (is_caliptra_secret_addr(partitions[i].address)) {
            VPRINTF(LOW, "INFO:: Got the secret partition with index %d and address 0x%x\n", i, partitions[i].address);
            VPRINTF(LOW, "INFO:: Skipping provisioning of secret partition in debug mode.\n");
            continue; // You cannot provision secret fuses in debug mode
        }
        VPRINTF(LOW, "INFO:: Trying to modify already locked fuse.\n");
        if (partitions[i].sw_digest || partitions[i].hw_digest) {
            dai_wr(rnd_fuse_addresses[i], sentinel, 0, partitions[i].granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK);
        }

        reset_fc_lcc_rtl();
        wait_dai_op_idle(0);
    } 
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    transition_state_check(TEST_UNLOCKED0, raw_unlock_token);

    test_unlocked0_provision();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
