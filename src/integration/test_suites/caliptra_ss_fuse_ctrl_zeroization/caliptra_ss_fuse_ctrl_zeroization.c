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
 * This function goes through a fuse controller zeroization sequence
 * (using the input port and the LCC scrap state). This actual broadcast
 * signal cannot be observed in software and must be verified through assertions.
 */
void zeroize() {
    uint32_t data[2];

    const partition_t hw_part = partitions[SECRET_LC_TRANSITION_PARTITION];

    dai_zer(hw_part.address, &data[0], &data[1], hw_part.granularity, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: fuse is not zeroized\n");
        goto epilogue;
    }
    memset(data, 0, 2*sizeof(uint32_t));
    // Zeroize marker field.
    dai_zer(hw_part.zer_address, &data[0], &data[1], 64, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: digest is not zeroized\n");
        goto epilogue;
    }
    memset(data, 0, 2*sizeof(uint32_t));

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

epilogue:
    VPRINTF(LOW, "zeroization test finished\n");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    transition_state(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);
    wait_dai_op_idle(0);

    initialize_otp_controller();
    wait_dai_op_idle(0);

    zeroize();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}