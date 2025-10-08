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
   This tests:
   1 - writes 0x55 to all entries of partition HEK0
   2 - Writes and reads the digest
   3 - Reset
   4 - zeroizes the entire partition (fuses, marker and digest)
 */

bool write_partition_zeroize(void) {
    uint32_t r_data[2];

    // Step 1 - writes 0x55 to all entries of partition HEK0
    VPRINTF(LOW, "==========================================\n");
    VPRINTF(LOW, "Writing partition HEK0 with 0x55 in each entry:\n");
    VPRINTF(LOW, "==========================================\n");
    for (uint32_t addr = partitions[CPTRA_SS_LOCK_HEK_PROD_0].address; addr < partitions[CPTRA_SS_LOCK_HEK_PROD_0].digest_address; addr += partitions[CPTRA_SS_LOCK_HEK_PROD_0].granularity / 8) {
      dai_wr(addr, 0x55, 0x55, 32, 0);
      dai_rd(addr, &r_data[0], &r_data[1], 32, 0);
      if (r_data[0] != 0x55) {
        VPRINTF(LOW, "ERROR: [CPTRA_SS_LOCK_HEK_PROD_0] read_value, does not match written_value\n");
        return false;
      }
    }


    // Step 2 - Write, then read the digest for HEK0 - which locks the partition
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_0].digest_address, 0xFF, 0xFF, 64, 0);
    memset(r_data, 0, sizeof(r_data));
    dai_rd(partitions[CPTRA_SS_LOCK_HEK_PROD_0].digest_address, &r_data[0], &r_data[1], 64, 0);
    if (r_data[0] != 0xFF || r_data[1] != 0xFF) {
      VPRINTF(LOW, "ERROR: Digest in partitions[CPTRA_SS_LOCK_HEK_PROD_0] read_value, does not match written_value\n");
      return 0;
    }

    VPRINTF(LOW, "=========================================================\n");
    VPRINTF(LOW, "Digest for HEK0 partitions has been written and read back\n");
    VPRINTF(LOW, "=========================================================\n");

    // Step 3 - Reset
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    VPRINTF(LOW, "==========================================\n");
    VPRINTF(LOW, "After after reset and DAI idle:\n");
    VPRINTF(LOW, "==========================================\n");




    // Step 4 - zeroizes the entire partition (fuses, marker and digest)
    VPRINTF(LOW, "=======================================================\n");
    VPRINTF(LOW, "Zeroizing fuses, markers and digest for partition HEK0:\n");
    VPRINTF(LOW, "=======================================================\n");

    // Zeroize fuse.
    for (uint32_t addr = partitions[CPTRA_SS_LOCK_HEK_PROD_0].address; addr < partitions[CPTRA_SS_LOCK_HEK_PROD_0].digest_address; addr += partitions[CPTRA_SS_LOCK_HEK_PROD_0].granularity / 8) {
        if (!dai_zer(addr, partitions[CPTRA_SS_LOCK_HEK_PROD_0].granularity, 0, false)) {
        VPRINTF(LOW, "ERROR: [partitions[CPTRA_SS_LOCK_HEK_PROD_0] ]fuse is not zeroized (pre-digest)\n");
        return false;
      }
    }
    // Zeroize marker field.
    if (!dai_zer(partitions[CPTRA_SS_LOCK_HEK_PROD_0].zer_address, 64, 0, false)) {
      VPRINTF(LOW, "ERROR: [partitions[CPTRA_SS_LOCK_HEK_PROD_0]  digest is not zeroized (post-digest)\n");
      return false;
    }
    // Zeroize digest field.
    if (!dai_zer(partitions[CPTRA_SS_LOCK_HEK_PROD_0].digest_address, 64, 0, false)) {
      VPRINTF(LOW, "ERROR: [partitions[CPTRA_SS_LOCK_HEK_PROD_0]  digest is not zeroized (post-digest)\n");
      return false;
    }

    VPRINTF(LOW, "ratchet seed write read test finished\n");
    return true;
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    initialize_otp_controller();

    VPRINTF(LOW, "=================\nBefore ratchet_seed_write_read\n=================\n\n");
    write_partition_zeroize();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
