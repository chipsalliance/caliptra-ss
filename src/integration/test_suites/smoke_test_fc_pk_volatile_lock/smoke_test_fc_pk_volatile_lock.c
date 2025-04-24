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

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

/**
 * Program two fuses in `VENDOR_HASHES_PROD_PARTITION`, then verify whether
 * the volatile lock works as intended. The test proceeds in the following steps:
 * 
 *   1. Write a value to first fuse.
 *   2. Write a value to second fuse.
 *   3. Activate the volatile lock such that the fuse from step 2 is now in the
 *      locked region.
 *   4. Verify that writing to the second fuse now results in an error.
 */
void program_vendor_hashes_prod_partition(void) {

    // 0x6C8: CPTRA_CORE_VENDOR_PK_HASH_3
    // 0x6E4: CPTRA_CORE_VENDOR_PK_HASH_5
    const uint32_t addresses[2] = {0x682, 0x6E4};

    const uint32_t data = 0xdeadbeef;

    // Step 1
    dai_wr(addresses[0], data, 0, 32, 0);

    // Step 2
    dai_wr(addresses[1], data+1, 0, 32, 0);

    // Step 3
    lsu_write_32(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, 4); // Lock all hashes starting from index 5.

    // Step 4
    dai_wr(addresses[1], data+2, 0, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
    
    lcc_initialization();
    // Set AXI user ID to MCU.
    grant_mcu_for_fc_writes(); 

    transition_state_check(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);

    initialize_otp_controller();

    program_vendor_hashes_prod_partition();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}