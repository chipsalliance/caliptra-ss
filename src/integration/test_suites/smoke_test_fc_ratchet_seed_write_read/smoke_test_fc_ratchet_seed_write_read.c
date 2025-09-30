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

// Write the 64-bit word wdata0/wdata1 to the given address in partition, then read it back to check
// the value is now equal to exp_rdata.
//
// exp_write_error is the expected error code when doing the DAI write. The read does not expect an
// error.
//
// If an error code or data read back is not as expected, return false (allowing a calling loop to
// stop early after an error)
bool write_read_partition_word(const partition_t *p,
                               uint32_t           addr,
                               const uint32_t    *wdata,
                               const uint32_t    *exp_rdata,
                               uint32_t           exp_write_error) {
    uint32_t rdata[2];
    if (!dai_wr(addr, wdata[0], wdata[1], p->granularity, exp_write_error)) return false;
    if (!dai_rd(addr, &rdata[0], &rdata[1], p->granularity, 0)) return false;

    if (rdata[0] != exp_rdata[0]) {
        VPRINTF(LOW,
                ("ERROR: Write/read failed for lower bytes of word at address 0x%0X in partition %0d. "
                 "Expected 0x%0X but read 0x%0X"),
                addr, p->index, exp_rdata[0], rdata[0]);
        return false;
    }

    if (p->granularity > 32 && rdata[1] != exp_rdata[1]) {
        VPRINTF(LOW,
                ("ERROR: Write/read failed for upper bytes of word at address 0x%0X in partition %0d. "
                 "Expected 0x%0X but read 0x%0X"),
                addr, p->index, exp_rdata[1], rdata[1]);
        return false;
    }

    return true;
}

// Write a word to each location in partition p, reading it back to check the value is as expected.
// This uses write_read_partition_word, which documents the wdata, exp_rdata and exp_write_error
// arguments.
//
// If an error code or rdata is not as expected, stops and returns false. Otherwise, returns true
// when the whole partition has been checked.
bool write_read_partition(const partition_t *p,
                          const uint32_t    *wdata,
                          const uint32_t    *exp_rdata,
                          uint32_t           exp_write_error) {
    VPRINTF(LOW, "  Doing write/read check for partition %0d\n", p->index);

    for (uint32_t addr = p->address; addr < p->digest_address; addr += p->granularity / 8) {
        if (!write_read_partition_word(p, addr, wdata, exp_rdata, exp_write_error)) return false;
    }
    return true;
}

// Apply write_read_partition to each partition with index between part0 and
// partN (inclusive). The wdata, exp_rdata and exp_write_error arguments are the same as
// for write_read_partition.
//
// As with the other functions, return false immediately if a write_read_partition call returns
// false.
bool write_read_block_of_partitions(uint32_t        part0,
                                    uint32_t        partN,
                                    const uint32_t *wdata,
                                    const uint32_t *exp_rdata,
                                    uint32_t        exp_write_error) {
    VPRINTF(LOW, " Write/read test for partitions %0d..%0d\n", part0, partN);
    for (uint32_t i = part0; i <= partN; i++) {
        if (!write_read_partition(&partitions[i], wdata, exp_rdata, exp_write_error)) {
            return false;
        }
    }
    return true;
}

// Write 0xff as a digest for partition p, then read the value back to check the digest was written.
bool write_read_digest(const partition_t *p) {
    uint32_t r_data[2] = {0, 0};
    VPRINTF(LOW, "  Doing write/read check for digest %0d\n", p->index);

    dai_wr(p->digest_address, 0xFF, 0xFF, 64, 0);
    dai_rd(p->digest_address, &r_data[0], &r_data[1], 64, 0);

    if (r_data[0] != 0xFF || r_data[1] != 0xFF) {
        VPRINTF(LOW, "ERROR: Unexpected value in digest %0d: 0x%0X, 0x%0X not 0xff, 0xff\n",
                p->index, r_data[0], r_data[1]);
        return false;
    }
    return true;
}

// Apply write_read_digest to each partition with index between part0 and partN
// (inclusive). As with the other functions, return false immediately if a write_read_digest call
// returns false.
bool write_read_block_of_digests(uint32_t part0, uint32_t partN) {
    VPRINTF(LOW, " Write/read test for digests %0d..%0d\n", part0, partN);
    for (uint32_t i = part0; i <= partN; i++) {
        if (!write_read_digest(&partitions[i])) return false;
    }
    return true;
}

// Zeroizes the fuse, marker and digest
bool zeroize_partition(const partition_t *p) {
    // Zeroize each fuse, reading back the response from the zeroize command. Check that is all
    // ones.
    VPRINTF(LOW, "  Zeroizing all the fuses in partition %0d\n", p->index);
    for (uint32_t addr = p->address; addr < p->digest_address; addr += p->granularity / 8) {
        if (!dai_zer(addr, p->granularity, 0, false)) return false;
    }

    // Zeroize marker field.
    VPRINTF(LOW, "  Zeroizing the marker field of partition %0d\n", p->index);
    if (!dai_zer(p->zer_address, 64, 0, false)) return false;

    // Zeroize digest field.
    VPRINTF(LOW, "  Zeroizing the digest field of partition %0d\n", p->index);
    if (!dai_zer(p->digest_address, 64, 0, false)) return false;

    return true;
}

bool zeroize_block_of_partitions(uint32_t part0, uint32_t partN) {
    VPRINTF(LOW, " Zeroize test for partitions %0d..%0d\n", part0, partN);
    for (uint32_t i = part0; i <= partN; i++) {
        if (!zeroize_partition(&partitions[i])) return false;
    }
    return true;
}

/*
  Apply a ratchet check for a block of HEK partitions.

    1. Write to each ratchet seed in the block and check the write worked.

    2. Write the digest for each HEK in the block, which locks the partition. Read it back again to
       check the digest was written correctly.

    3. Write some other value to each ratchet seed in the block and check a DAI error is returned.
       Read the seed back each time and check the result is the value we wrote before.

    4. Zeroize each partition

  If any of the steps fails then exit immediately, returning false.
 */
bool ratchet_check_for_block(uint32_t part0, uint32_t partN) {
    uint32_t wdata_gen0[2] = {0x03, 0x03};
    uint32_t wdata_gen1[2] = {0xf0, 0xf0};

    // Step 1: Write to each HEK one by one and read back the values written
    VPRINTF(LOW, "================================\n");
    VPRINTF(LOW, "Step 1/5: Write/Read of HEKs\n");
    VPRINTF(LOW, "================================\n");
    if (!write_read_block_of_partitions(part0, partN, wdata_gen0, wdata_gen0, 0))
        return false;

    // Step 2: Write the digest for each HEK (and then read it back). This locks each partition.
    VPRINTF(LOW, "===============================\n");
    VPRINTF(LOW, "Step 2/5: Write HEK digests\n");
    VPRINTF(LOW, "===============================\n");
    if (!write_read_block_of_digests(part0, partN))
        return false;

    // Step 3: Apply reset
    //
    // At this point, all the digests have been written and the HEK partitions have been locked.
    // Apply a reset and wait for DAI to become idle again.
    VPRINTF(LOW, "==================================================\n");
    VPRINTF(LOW, "Step 3/5: All digests written. Applying reset.\n");
    VPRINTF(LOW, "==================================================\n");

    reset_fc_lcc_rtl();
    if (!wait_dai_op_idle(0))
        return false;

    // Step 4: Try the write/read dance from step 1 but with different wdata.
    //
    // We now expect each write to fail with DAI_ERROR and the values on reading to be those written
    // in step 1.
    VPRINTF(LOW, "=======================================\n");
    VPRINTF(LOW, "Step 4/5: Write/Read to locked HEKs\n");
    VPRINTF(LOW, "=======================================\n");
    if (!write_read_block_of_partitions(part0, partN, wdata_gen1, wdata_gen0,
                                        OTP_CTRL_STATUS_DAI_ERROR_MASK))
        return false;

    // Step 5: Zeroize all the HEK partitions
    VPRINTF(LOW, "================================================\n");
    VPRINTF(LOW, "Step 5/5: Zeroize fuses and markers for HEKs\n");
    VPRINTF(LOW, "================================================\n");
    if (!zeroize_block_of_partitions(part0, partN))
        return false;

    return true;
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    initialize_otp_controller();

    VPRINTF(LOW, "=================\nAbout to do ratchet check\n=================\n\n");

    // We want to pick a random consecutive pair of partitions from
    // CPTRA_SS_LOCK_HEK_PROD_0..CPTRA_SS_LOCK_HEK_PROD_7. To do that, we just pick index of the
    // lower value to be something in the range 0..6 and use xorshift32() to get a random value.
    unsigned first_idx = xorshift32() % 7;

    ratchet_check_for_block(CPTRA_SS_LOCK_HEK_PROD_0 + first_idx,
                            CPTRA_SS_LOCK_HEK_PROD_0 + first_idx + 1);

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
