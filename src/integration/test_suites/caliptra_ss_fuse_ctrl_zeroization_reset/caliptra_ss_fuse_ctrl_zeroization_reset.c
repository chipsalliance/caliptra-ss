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
        uint32_t exp_status) {

    uint32_t act_data[2];
    int mismatches = 0;

    // Read and compare the data, for which the granularity and size
    // depend on the partition.
    for (uint32_t addr = part->address;
            addr < part->digest_address;
            addr += part->granularity / 8) {
        dai_rd(addr, &act_data[0], &act_data[1], part->granularity, exp_status);
        mismatches += compare(act_data[0], exp_data[0], addr);
        // Check second 32 bit only if the partition has a granularity
        // of more than 32 bit.
        if (part->granularity > 32) {
            mismatches += compare(act_data[1], exp_data[1], addr + 4);
        }
    }

    // Read and compare the digest, which always has a granularity and
    // size of 64 bit.
    dai_rd(part->digest_address, &act_data[0], &act_data[1], 64, exp_status);
    mismatches += compare(act_data[0], exp_data[0], part->digest_address);
    mismatches += compare(act_data[1], exp_data[1], part->digest_address + 4);

    return mismatches;
}

int part_zeroize(
        const partition_t* part,
        uint8_t only_until_half_data,
        uint32_t exp_status) {
    uint32_t rdata[2];
    int mismatches = 0;

    // Firstly, zeroize the zeroization marker, which always has a
    // granularity and size of 64 bit.
    dai_zer(part->zer_address, &rdata[0], &rdata[1], 64, exp_status);
    mismatches += compare(rdata[0], 0xFFFFFFFF, part->zer_address);
    mismatches += compare(rdata[1], 0xFFFFFFFF, part->zer_address + 4);

    // Secondly, zeroize the data, for which the granularity and size
    // depend on the partition.
    uint32_t addr_bound = part->digest_address;
    if (only_until_half_data) {
        // In this case, set the address bound half way between the
        // digest address and the base address.
        addr_bound -= (part->digest_address - part->address) / 2;
    }

    for (uint32_t addr = part->address;
            addr < addr_bound;
            addr += part->granularity / 8) {
        dai_zer(addr, &rdata[0], &rdata[1], part->granularity, exp_status);
        mismatches += compare(rdata[0], 0xFFFFFFFF, addr);
        // Check second 32 bit only if the partition has a granularity
        // of more than 32 bit.
        if (part->granularity > 32) {
            mismatches += compare(rdata[1], 0xFFFFFFFF, addr + 4);
        }
    }

    if (!only_until_half_data) {
        // Finally, zeroize the digest, which always has a granularity and
        // size of 64 bit.
        dai_zer(part->digest_address, &rdata[0], &rdata[1], 64, exp_status);
        mismatches += compare(rdata[0], 0xFFFFFFFF, part->digest_address);
        mismatches += compare(rdata[1], 0xFFFFFFFF, part->digest_address + 4);
    }

    return mismatches;
}

int check_part_zeroized(
        const partition_t* part,
        uint8_t only_marker,
        uint32_t exp_status) {
    uint32_t exp_ones[] = {0xFFFFFFFF, 0xFFFFFFFF};
    int mismatches = 0;

    if (!only_marker) {
        // Read and compare the data and digest.
        mismatches += part_read_compare(part, exp_ones, 0);
    }

    // Read the partition zeroization marker and check that the result
    // is all ones.
    uint32_t act_data[2];
    dai_rd(part->zer_address, &act_data[0], &act_data[1], 64, 0);
    mismatches += compare(act_data[0], exp_ones[0], part->zer_address) != 0;
    mismatches += compare(act_data[0], exp_ones[0], part->zer_address) != 0;

    return mismatches;
}

int prepare_test(const partition_t* part, uint32_t rd_lock_csr_addr) {
    // Initialize test constants.
    const uint32_t exp_data[] = {0xA5A5A5A5, 0x96969696};

    // Step 1: Write the partition.
    for (uint32_t addr = part->address;
            addr < part->digest_address;
            addr += part->granularity / 8) {
        dai_wr(addr, exp_data[0], exp_data[1], part->granularity, 0);
    }

    // Step 2: Write the digest (doesn't have to be and isn't a real
    // digest value).
    dai_wr(part->digest_address, exp_data[0], exp_data[1], 64, 0);

    // Step 3: Reset.
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Step 4: Read the written value back.
    // First ensure that the read lock CSR is currently not set.
    uint32_t csr = lsu_read_32(rd_lock_csr_addr);
    if (csr != 1) {
        VPRINTF(LOW, "TEST BUG: Partition is read-locked!\n");
        return 2;
    }
    // Then read the value back and compare it.
    if (part_read_compare(part, exp_data, 0) != 0) {
        VPRINTF(LOW, "ERROR: Step 4 failed!\n");
        return 1;
    }

    // Step 5: Activate the read lock CSR.
    lsu_write_32(rd_lock_csr_addr, 0);

    // Step 6: Verify that reading the partition now gives an access
    // error and returns zeros.
    uint32_t exp_zeros[] = {0, 0};
    if (part_read_compare(part, exp_zeros, OTP_CTRL_STATUS_DAI_ERROR_MASK)
            != 0) {
        VPRINTF(LOW, "ERROR: Step 6 failed!\n");
        return 1;
    }

    // Step 7: Reset again.
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    return 0;
}

int end_test(const partition_t* part) {
    // Note that the data and digest of the zeroized partition cannot be
    // read without a reset, as this would result in ECC errors. This is
    // not a problem because in Step 8, SW checked the result of
    // zeroization and ensured that all fuses are now set to `1` also
    // for the data and digest part of the partition.

    // Step 10: Reset.
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Step 11: Read and check that everything in the partition is all
    // ones.
    if (check_part_zeroized(part, /*only_marker=*/0, 0) != 0) {
        VPRINTF(LOW, "ERROR: Final step failed!\n");
        return 1;
    }
}

int test_normal_zeroization (void) {
    // Choose one of the zeroizable SW partitions with a CSR read lock.
    const partition_t part = partitions[CPTRA_SS_LOCK_HEK_PROD_3];
    const uint32_t rd_lock_csr_addr =
            SOC_OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_READ_LOCK;

    int retval = prepare_test(&part, rd_lock_csr_addr);
    if (retval != 0) {
        return retval;
    }

    // Step 8: Zeroize the partition.
    if (part_zeroize(&part, /*only_until_half_data=*/0, 0) != 0) {
        VPRINTF(LOW, "ERROR: Step 8 failed!\n");
        return 1;
    }

    // Step 9: Read the zeroization marker through the DAI. In the
    // previous step, SW already checked that the zeroization marker
    // returned by the zeroization command is all ones. A different
    // piece of SW might at a later point before a reset want to check
    // the zeroization status for a partition, and this is what this
    // step emulates.
    if (check_part_zeroized(&part, /*only_marker=*/1, 0) != 0) {
        VPRINTF(LOW, "ERROR: Step 9 failed!\n");
        return 1;
    }

    return end_test(&part);
}

int test_half_zeroization (void) {
    // Choose another zeroizable SW partition with a CSR read lock.
    const partition_t part = partitions[CPTRA_SS_LOCK_HEK_PROD_5];
    const uint32_t rd_lock_csr_addr =
            SOC_OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_READ_LOCK;

    int retval = prepare_test(&part, rd_lock_csr_addr);
    if (retval != 0) {
        return retval;
    }

    // Step 8: Zeroize the partition, but only until half the data.
    if (part_zeroize(&part, /*only_until_half_data=*/1, 0) != 0) {
        VPRINTF(LOW, "ERROR: Step 8 failed!\n");
        return 1;
    }

    // Step 9: Reset. This is to emulate that a reset happened while
    // SW was zeroizing the partition.
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Step 10: Read the zeroization marker, which should indicate that
    // zeroization has been started on the partition.
    if (check_part_zeroized(&part, /*only_marker=*/1, 0) != 0) {
        VPRINTF(LOW, "ERROR: Step 10 failed!\n");
        return 1;
    }

    // Step 11: Zeroize the entire partition again, this time entirely.
    if (part_zeroize(&part, /*only_until_half_data=*/0, 0) != 0) {
        VPRINTF(LOW, "ERROR: Step 11 failed!\n");
        return 1;
    }

    return end_test(&part);
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")

    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    lcc_initialization();
    grant_mcu_for_fc_writes();

    VPRINTF(LOW, "INFO: caliptra_ss_fuse_ctrl_zeroization_reset code.\n");

    VPRINTF(LOW, "INFO: Starting normal zeroization test.\n");
    int result = test_normal_zeroization();
    if (result == 0) {
        VPRINTF(LOW, "INFO: Test PASSED\n");
    } else {
        VPRINTF(LOW, "ERROR: Test FAILED\n")
    }

    VPRINTF(LOW, "INFO: Starting half-partition zeroization test.\n");
    result = test_half_zeroization();
    if (result == 0) {
        VPRINTF(LOW, "INFO: Test PASSED\n");
    } else {
        VPRINTF(LOW, "ERROR: Test FAILED\n")
    }

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}