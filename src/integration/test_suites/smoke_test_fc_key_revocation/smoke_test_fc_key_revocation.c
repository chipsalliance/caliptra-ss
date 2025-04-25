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
 * Program the revocation bits in `VENDOR_REVOCATIONS_PROD_PARTITION`. The test
 * proceeds in the following steps:
 * 
 *   1. Write a value to a fuse.
 *   2. Read back the value and verify it is equal to the value written in Step 1.
 *   3. Write a dummy digest into the partition's digest field, which locks the
 *      partition. This works since it is an unbuffered software partition.
 *   4. Reset the RTL.
 *   5. Read back the fuse again and verify that the value has not changed, i.e.,
 *      is equal to the value written in Step 1.
 *   6. Try to write a value into the fuse and verify that it results in an error
 *      as the partition has been locked in Step 3.
 *   7. Read back the digest from the partition's digest register and verify it
 *      is equal to the dummy digest written in Step 3.
 */
void vendor_revocations_prod_partition() {

    // 0x910: CPTRA_CORE_ECC_REVOCATION_0
    const uint32_t base_address = 0x910;
    const uint32_t digest_address = 0x9A0;
    const uint32_t fuse_address = base_address;

    const uint32_t data = 0xdeadbeef;
    uint32_t read_data;

    uint32_t status = 0;

    // Step 1
    dai_wr(fuse_address, data, 0, 32, 0);

    // Step 2
    dai_rd(fuse_address, &read_data, NULL, 32, 0);
    if (data != read_data) {
        VPRINTF(LOW, "ERROR: incorrect fuse data: expected: %08X actual: %08X\n", data, read_data);
        exit(1);
    }

    // Step 3
    dai_wr(digest_address, 0xff, 0xff, 64, 0);

    // Step 4
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Step 5
    dai_rd(fuse_address, &read_data, NULL, 32, 0);
    if (data != read_data) {
        VPRINTF(LOW, "ERROR: incorrect fuse data: expected: %08X actual: %08X\n", data, read_data);
        exit(1);
    }

    // Step 6
    dai_wr(fuse_address, data, 0, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);

    // Step 7
    uint32_t digest[2];
    digest[0] = lsu_read_32(SOC_OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_DIGEST_0);
    digest[1] = lsu_read_32(SOC_OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_DIGEST_1);
    if (digest[0] == 0 && digest[1] == 0) {
        VPRINTF(LOW, "ERROR: digest is 0\n");
        exit(1);
    }
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

    vendor_revocations_prod_partition();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}