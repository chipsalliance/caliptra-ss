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
#include "fuse_ctrl_mmap.h"
#include "lc_ctrl.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

int compare(uint32_t actual, uint32_t expected, uint32_t address) {
    if (actual != expected) {
        VPRINTF(LOW, "ERROR: @0x%08X: 0x%08X != 0x%08X\n",
                address, actual, expected);
        return 1;
    }
    return 0;
}
int part_read_compare(
        const partition_t* part,
        const uint32_t* exp_data,
        uint32_t exp_status,
        uint8_t include_digest
    ) {

    uint32_t act_data[2];
    int mismatches = 0;

    // Read and compare the data, for which the granularity and size
    // depend on the partition.
    for (uint32_t addr = part->address;
            addr < part->digest_address;
            addr += part->granularity) {
        dai_rd(addr, &act_data[0], &act_data[1], part->granularity, exp_status);
        mismatches += compare(act_data[0], exp_data[0], addr);
        // Check second 32 bit only if the partition has a granularity
        // of more than 32 bit.
        if (part->granularity > 32) {
            mismatches += compare(act_data[1], exp_data[1], addr + 4);
        }
    }

    if (include_digest) {
        // Read and compare the digest, which always has a granularity and
        // size of 64 bit.
        dai_rd(part->digest_address, &act_data[0], &act_data[1], 64, exp_status);
        mismatches += compare(act_data[0], exp_data[0], part->digest_address);
        mismatches += compare(act_data[1], exp_data[1], part->digest_address + 4);
    }

    return mismatches;
}

int part_zeroize(const partition_t* part, uint32_t exp_status) {
    uint32_t rdata[2];
    int mismatches = 0;

    // Firstly, zeroize the zeroization marker, which always has a
    // granularity and size of 64 bit.
    dai_zer(part->zer_address, &rdata[0], &rdata[1], 64, exp_status);
    mismatches += compare(rdata[0], 0xFFFFFFFF, part->zer_address);
    mismatches += compare(rdata[1], 0xFFFFFFFF, part->zer_address + 4);

    // Secondly, zeroize the data, for which the granularity and size
    // depend on the partition.
    for (uint32_t addr = part->address;
            addr < part->digest_address;
            addr += part->granularity) {
        dai_zer(addr, &rdata[0], &rdata[1], part->granularity, exp_status);
        mismatches += compare(rdata[0], 0xFFFFFFFF, addr);
        // Check second 32 bit only if the partition has a granularity
        // of more than 32 bit.
        if (part->granularity > 32) {
            mismatches += compare(rdata[1], 0xFFFFFFFF, addr + 4);
        }
    }

    // Finally, zeroize the digest, which always has a granularity and
    // size of 64 bit.
    dai_zer(part->digest_address, &rdata[0], &rdata[1], 64, exp_status);
    mismatches += compare(rdata[0], 0xFFFFFFFF, part->digest_address);
    mismatches += compare(rdata[1], 0xFFFFFFFF, part->digest_address + 4);

    return mismatches;
}

int check_part_zeroized(const partition_t* part, uint32_t exp_status) {
    uint32_t exp_ones[] = {0xFFFFFFFF, 0xFFFFFFFF};
    int mismatches = 0;

    // Read and compare the data and digest.
    mismatches += part_read_compare(part, exp_ones, 0, 1);

    // Read the partition zeroization marker and check that the result
    // is all ones.
    uint32_t act_data[2];
    dai_rd(part->zer_address, &act_data[0], &act_data[1], 64, 0);
    mismatches += compare(act_data[0], exp_ones[0], part->zer_address) != 0;
    mismatches += compare(act_data[0], exp_ones[0], part->zer_address) != 0;

    return mismatches;
}

/**
 * This test emulates OTP corruption due to reset during programming
 * and checks that zeroization is still possible in this case.
 */
void test_main (void) {
    // Initialize test constants.
    const uint32_t wr_data0[] = {0x11111111, 0x44444444};
    const uint32_t wr_data1[] = {0x33333333, 0xCCCCCCCC};
    const uint32_t exp_data[] = {
            wr_data0[0] | wr_data1[0],
            wr_data0[1] | wr_data1[1]
    };

    // Choose one of the zeroizable SW partitions.
    const partition_t part = partitions[CPTRA_SS_LOCK_HEK_PROD_0];

    // Step 1: Write the data fuses of the partition twice with
    // different values.

    // The first write sequence will go through without errors.
    for (uint32_t addr = part.address;
            addr < part.digest_address;
            addr += part.granularity / 8) {
        dai_wr(addr, wr_data0[0], wr_data0[1], part.granularity, 0);
    }
    // The second write sequence will trigger writeblank errors due to
    // ECC bits being toggled from 1 to 0. The writes *will* update the
    // words with an invalid ECC portion.
    for (uint32_t addr = part.address;
            addr < part.digest_address;
            addr += part.granularity / 8) {
        dai_wr(addr, wr_data1[0], wr_data1[1], part.granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    }

    // Step 2: Check that reading the data fuses now returns an
    // integrity error due to the second write in Step 1 corrupting
    // the ECC part of each word.
    if (part_read_compare(&part, exp_data, OTP_CTRL_STATUS_DAI_ERROR_MASK, 0) != 0) {
        VPRINTF(LOW, "ERROR: Step 2 failed!\n");
        goto epilogue;
    }

    // Step 3: Reset.
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Step 4: Zeroize and check that zeroization succeeded.
    if (part_zeroize(&part, 0) != 0) {
        VPRINTF(LOW, "ERROR: Step 4 failed!\n");
        goto epilogue;
    }

    // Step 5: Reset.
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Step 6: Read the partition back and ensure its now all ones.
    if (check_part_zeroized(&part, 0) != 0) {
        VPRINTF(LOW, "ERROR: Step 6 failed!\n");
        goto epilogue;
    }

epilogue:
    VPRINTF(LOW, "caliptra_ss_fuse_ctrl_zeroization_corrupt test finished\n");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")

    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    lcc_initialization();
    grant_mcu_for_fc_writes();

    test_main();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}