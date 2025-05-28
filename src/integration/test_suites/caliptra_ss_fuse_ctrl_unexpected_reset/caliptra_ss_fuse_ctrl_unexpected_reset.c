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

/**
 * This function verifies that partitions remain unlocked after
 * a reset when no locking command has been issued.
 */
void unexpected_reset() {
    const uint32_t sentinel = 0x01;

    partition_t partition = partitions[xorshift32() % (NUM_PARTITIONS-1)];

    if (partition.address > 0x40 && partition.address < 0xD0) {
        grant_caliptra_core_for_fc_writes();
    } else {
        grant_mcu_for_fc_writes(); 
    }

    dai_wr(partition.address, sentinel, 0x0, partition.granularity, 0);

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Check that the partition remains unlocked after the reset.
    // For software partitions are write should succeed while for
    // hardware partitions a read should go through.
    if (!partition.is_secret) {
        dai_wr(partition.address, sentinel, 0x0, partition.granularity, 0);
    } else {
        uint32_t read_data[2];
        dai_rd(partition.address, &read_data[0], &read_data[1], partition.granularity, 0);
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

    unexpected_reset();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
