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
 * Program a LCC transition token in `SECRET_LC_TRANSITION_PARTITION` and verify
 * that the valid bit is asserted once the partition has been locked. The test
 * proceeds in the following steps:
 * 
 *   1. Write a full transition token into the partition.
 *   2. Read back the token and verify it is equal to the token written in Step 1.
 *      This works as long as the secret partition has not been locked.
 *   3. Verify that the partition's digest register is 0.
 *   4. Lock the partition by calculating a hardware digest.
 *   5. Reset the RTL.
 *   6. Try to read the token and verify that it results in an error as the
 *      partition is secret and locked, thus not accessible by software anymore.
 *   7. Try to write a value into the partition and verify that it results in an error
 *      as the partition has been locked in Step 5.
 *   8. Read back the digest from the partition's digest register and verify it
 *      is non-zero.
 *   9. Use a backdoor channel to verify that the valid bit is set.
 */
void program_secret_lc_transition_partition() {

    // 0x4C0: CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN
    const uint32_t base_address = 0x4C0;
    const uint32_t fuse_address = 0x540;

    const uint32_t data[4] = {0xdeadbeef, 0xcafebabe, 0x12345678, 0xabababab};
    uint32_t read_data[4];

    // Step 1
    dai_wr(fuse_address, data[0], data[1], 64, 0);
    dai_wr(fuse_address+8, data[2], data[3], 64, 0);

    // Step 2
    dai_rd(fuse_address, &read_data[0], &read_data[1], 64, 0);
    dai_rd(fuse_address+8, &read_data[2], &read_data[3], 64, 0);
    if (memcmp(data, read_data, 16)) {
        VPRINTF(LOW, "ERROR: incorrect fuse data: expected: %08X actual: %08X\n", data[2], read_data[2]);
        exit(1);
    }

    // Step 3
    uint32_t digest[2];
    digest[0] = lsu_read_32(SOC_OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_DIGEST_0);
    digest[1] = lsu_read_32(SOC_OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_DIGEST_1);
    if (digest[0] != 0 || digest[1] != 0) {
        VPRINTF(LOW, "ERROR: digest is not 0\n");
        exit(1);
    }

    // Step 4
    calculate_digest(base_address);

    // Step 5
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Step 6
    dai_rd(fuse_address, &read_data[0], &read_data[1], 64, OTP_CTRL_STATUS_DAI_ERROR_MASK);

    // Step 7
    dai_wr(fuse_address, data[0], data[1], 64, OTP_CTRL_STATUS_DAI_ERROR_MASK);

    // Step 8
    digest[0] = lsu_read_32(SOC_OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_DIGEST_0);
    digest[1] = lsu_read_32(SOC_OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_DIGEST_1);
    if (digest[0] == 0 && digest[1] == 0) {
        VPRINTF(LOW, "ERROR: digest is 0\n");
        exit(1);
    }

    // Step 9
    // Use backdoor channel to verify that the valid bit is set.
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

    program_secret_lc_transition_partition();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}