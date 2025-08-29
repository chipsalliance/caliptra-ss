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
   1 - writes 0x55 to all entries of a partition
   2 - zeroizes the partition
 */

void write_partition_zeroize(void) {
    uint32_t r_data[2];


    //=================================
    // Write - Read the ratchet seeds:
    //=================================
    VPRINTF(LOW, "==========================================\n");
    VPRINTF(LOW, "Writing partition HEK0 with 0x55 in each entry:\n");
    VPRINTF(LOW, "==========================================\n");

    for (uint32_t addr = partitions[CPTRA_SS_LOCK_HEK_PROD_0].address; addr < partitions[CPTRA_SS_LOCK_HEK_PROD_0].digest_address; addr += 4) {
      dai_wr(addr, 0x55, 0x55, 32, 0);
      dai_rd(addr, &r_data[0], &r_data[1], 32, 0);
      if (r_data[0] != 0x55) {
        VPRINTF(LOW, "ERROR: [CPTRA_SS_LOCK_HEK_PROD_0] read_value, does not match written_value\n");
        goto epilogue;
      }
    }


    // zeroize all the HEK partitions:
    VPRINTF(LOW, "==========================================\n");
    VPRINTF(LOW, "Zeroizing all the fuses and markers for partition HEK0:\n");
    VPRINTF(LOW, "==========================================\n");

    // Zeroize fuse.
    for (uint32_t addr = partitions[CPTRA_SS_LOCK_HEK_PROD_0].address; addr < partitions[CPTRA_SS_LOCK_HEK_PROD_0].digest_address; addr += 4) {
      dai_zer(addr, &r_data[0], &r_data[1], partitions[CPTRA_SS_LOCK_HEK_PROD_0].granularity, 0);
      if (r_data[0] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: [partitions[CPTRA_SS_LOCK_HEK_PROD_0] ]fuse is not zeroized (pre-digest)\n");
        goto epilogue;
      }
    }
    memset(r_data, 0, 2*sizeof(uint32_t));
    // Zeroize marker field.
    dai_zer(partitions[CPTRA_SS_LOCK_HEK_PROD_0].zer_address, &r_data[0], &r_data[1], 64, 0);
    if (r_data[0] != 0xFFFFFFFF || r_data[1] != 0xFFFFFFFF) {
      VPRINTF(LOW, "ERROR: [partitions[CPTRA_SS_LOCK_HEK_PROD_0]  digest is not zeroized (post-digest)\n");
      goto epilogue;
    }
    memset(r_data, 0, 2*sizeof(uint32_t));

epilogue:
    VPRINTF(LOW, "ratchet seed write read test finished\n");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    initialize_otp_controller();

    VPRINTF(LOW, "=================\nBefore ratchet_seed_write_read\n=================\n\n")
    write_partition_zeroize();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
