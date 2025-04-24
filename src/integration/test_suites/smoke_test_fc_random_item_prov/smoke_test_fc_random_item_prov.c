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
 * Program a randomized fuse in `SW_MANUF_PARTITION`. The function consists
 * of the following steps:
 * 
 *   1. Write a value to a randomized fuse.
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
void program_sw_manuf_partition(uint32_t seed) {

    // 0x0D0: CPTRA_CORE_ANTI_ROLLBACK_DISABLE
    // 0x0D1: CPTRA_CORE_IDEVID_CERT_IDEVID_ATTR
    // 0x131: CPTRA_CORE_IDEVID_MANUF_HSM_IDENTIFIER
    // 0x141: CPTRA_CORE_SOC_STEPPING_ID
    // 0x143: CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_0
    const uint32_t addresses[12] = {0x0D0, 0x0D1, 0x131, 0x141, 0x143, 0x173, 0x1A3, 0x1D3, 0x203, 0x233, 0x263, 0x293};
    const uint32_t digest_address = 0x4B8;
    uint32_t fuse_address = addresses[seed % 12];

    const uint32_t data = 0xAB;
    uint32_t read_data;

    // Step 1
    dai_wr(fuse_address, data, 0, 32, 0);

    // Step 2
    dai_rd(fuse_address, &read_data, NULL, 32, 0);
    if (data != read_data) {
        VPRINTF(LOW, "ERROR: incorrect fuse data: expected: %08X actual: %08X\n", data, read_data);
        exit(1);
    }

    // Step 3
    dai_wr(digest_address, 0xFF, 0xFF, 64, 0);

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
    digest[0] = lsu_read_32(SOC_OTP_CTRL_SW_MANUF_PARTITION_DIGEST_DIGEST_0);
    digest[1] = lsu_read_32(SOC_OTP_CTRL_SW_MANUF_PARTITION_DIGEST_DIGEST_1);
    if (digest[0] != 0xFF || digest[1] != 0xFF) {
        VPRINTF(LOW, "ERROR: digest is 0\n");
        exit(1);
    }

    VPRINTF(LOW, "DEBUG: program sw manuf successful\n");
}

/**
 * Program a randomized fuse in `VENDOR_SECRET_PROD_PARTITION`. The function consists
 * of the following steps:
 * 
 *   1. Write a value to a randomized fuse.
 *   2. Read back the value and verify it is equal to the value written in Step 1.
 *      This works as long as the secret partition has not been locked.
 *   3. Verify that the partition's digest register is 0.
 *   4. Lock the partition by calculating a hardware digest.
 *   5. Reset the RTL.
 *   6. Try to read the fuse and verify that it results in an error as the
 *      is secret and locked thus not accessible by software anymore.
 *   7. Try to write a value into the fuse and verify that it results in an error
 *      as the partition has been locked in Step 5.
 *   8. Read back the digest from the partition's digest register and verify it
 *      is non-zero.
 */
void program_vendor_secret_prod_partition(uint32_t seed) {
    // Set AXI user ID to 1.
    uint32_t axi_conf;
    axi_conf = lsu_read_32(0x70000080);

    const uint32_t base_address = 0x9A8;
    uint32_t fuse_address = base_address + 32*(seed % 15);

    const uint32_t data[2] = {0xdeadbeef, 0xcafebabe};
    uint32_t read_data[2];

    // Step 1
    dai_wr(fuse_address, data[0], data[1], 64, 0);

    // Step 2
    dai_rd(fuse_address, &read_data[0], &read_data[1], 64, 0);
    if (data[0] != read_data[0] || data[1] != read_data[1]) {
        VPRINTF(LOW, "ERROR: incorrect fuse data: expected: %08X actual: %08X\n", data, read_data);
        exit(1);
    }

    // Step 3
    uint32_t digest[2];
    digest[0] = lsu_read_32(SOC_OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_0);
    digest[1] = lsu_read_32(SOC_OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_1);
    if (digest[0] != 0 || digest[1] != 0) {
        VPRINTF(LOW, "ERROR: digest is not 0\n");
    }

    // Step 4
    calculate_digest(base_address);

    // Step 5
    reset_fc_lcc_rtl();

    // Step 6
    dai_rd(fuse_address, &read_data[0], &read_data[1], 64, OTP_CTRL_STATUS_DAI_ERROR_MASK);

    // Step 7
    dai_wr(fuse_address, data[0], data[1], 64, OTP_CTRL_STATUS_DAI_ERROR_MASK);

    // Step 8
    digest[0] = lsu_read_32(SOC_OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_0);
    digest[1] = lsu_read_32(SOC_OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_1);
    if (digest[0] == 0 && digest[1] == 0) {
        VPRINTF(LOW, "ERROR: digest is 0\n");
        exit(1);
    }

    VPRINTF(LOW, "DEBUG: program vendor secret prod successful\n");
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

    uint32_t rnd = xorshift32();

#ifdef PROGRAM_SECRET_PARTITON
    program_vendor_secret_prod_partition(rnd);
#else
    program_sw_manuf_partition(rnd);
#endif // PROGRAM_SECRET_PARTITION

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}