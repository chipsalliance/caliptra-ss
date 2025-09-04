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


// Writes the entire partition with values wdata0 and wdata1 and reads back the values written match the values read
bool write_read_entire_partition(uint32_t num_partition, uint32_t wdata0, uint32_t wdata1, uint32_t write_error_mask, uint32_t read_error_mask) {
  uint32_t rdata[2];

  for (uint32_t addr = partitions[num_partition].address; addr < partitions[num_partition].digest_address; addr += partitions[num_partition].granularity / 8) {
    dai_wr(addr, wdata0, wdata1, partitions[num_partition].granularity, write_error_mask);
    dai_rd(addr, &rdata[0], &rdata[1], partitions[num_partition].granularity, read_error_mask);
    if (rdata[0] != wdata0 || (partitions[num_partition].granularity > 32 && rdata[1] != wdata1)) {
      VPRINTF(LOW, "ERROR: partitions[num_partition=%0d] read_value, does not match written_value\n", num_partition);
      return false;
    }
  }
  return true;

}
// Zeroizes the fuse, marker and digest
bool zeroize_all_partition(uint32_t num_partition) {
  uint32_t r_data[2];


  memset(r_data, 0, sizeof(r_data));
  // Zeroize fuse.
  for (uint32_t addr = partitions[num_partition].address; addr < partitions[num_partition].digest_address; addr += partitions[num_partition].granularity / 8) {
    dai_zer(addr, &r_data[0], &r_data[1], partitions[num_partition].granularity, 0);
    if (r_data[0] != 0xFFFFFFFF  || (partitions[num_partition].granularity > 32 && r_data[1] != 0xFFFFFF)) {
      VPRINTF(LOW, "ERROR: [partitions[%0d] ]fuse is not zeroized\n",num_partition);
      return false;
    }
  }
  memset(r_data, 0, sizeof(r_data));
  // Zeroize marker field.
  dai_zer(partitions[num_partition].zer_address, &r_data[0], &r_data[1], 64, 0);
  if (r_data[0] != 0xFFFFFFFF || r_data[1] != 0xFFFFFFFF) {
    VPRINTF(LOW, "ERROR: [partitions[%0d] marker is not zeroized\n",num_partition);
    return false;
  }
  memset(r_data, 0, sizeof(r_data));
  // zeroize digest field.
  dai_zer(partitions[num_partition].digest_address, &r_data[0], &r_data[1], 64, 0);
  if (r_data[0] != 0xFFFFFFFF || r_data[1] != 0xFFFFFFFF) {
    VPRINTF(LOW, "ERROR: [partitions[%0d] digest is not zeroized\n",num_partition);
    return false;
  }
  memset(r_data, 0, sizeof(r_data));
  return true;
}


/**
   This tests:
   1 - writes to each ratchet seed one by one and reads back the value written was returned.
   2 - Write, then read the digest for all HEKs
   3 - tries writing and reading and checking a DAI error is returned
   4 - zeroize all the HEK fuses and markers
 */

void ratchet_seed_write_read(void) {
    uint32_t r_data[2];
    uint32_t w_data[2] = {0x03, 0x03};



    // Step 1 - writes to each ratchet seed one by one and reads back the value written was returned.
    VPRINTF(LOW, "==========================================\n");
    VPRINTF(LOW, "Doing Write/Read of HEKs:\n");
    VPRINTF(LOW, "==========================================\n");
    for (uint32_t partition_no = CPTRA_SS_LOCK_HEK_PROD_0; partition_no <= CPTRA_SS_LOCK_HEK_PROD_7; partition_no++) {
      if (write_read_entire_partition(partition_no, w_data[0], w_data[1], 0, 0) == false)
        goto epilogue;
    }


    // Step 2 - Write, then read the digest for all HEKs - which locks the partition
    for (uint32_t partition_no = CPTRA_SS_LOCK_HEK_PROD_0; partition_no <= CPTRA_SS_LOCK_HEK_PROD_7; partition_no++) {
      dai_wr(partitions[partition_no].digest_address, 0xFF, 0xFF, 64, 0);
      memset(r_data, 0, 2*sizeof(uint32_t));
      dai_rd(partitions[partition_no].digest_address, &r_data[0], &r_data[1], 64, 0);
      if (r_data[0] != 0xFF || r_data[1] != 0xFF) {
        VPRINTF(LOW, "ERROR: Digest in partitions[partition_no=%0d] read_value, does not match written_value\n", partition_no);
        return 0;
      }
    }

    VPRINTF(LOW, "=====================================================\n");
    VPRINTF(LOW, "All the digests for HEKs partitions have been written\n");
    VPRINTF(LOW, "=====================================================\n");


    //=================================
    // Reset:
    //=================================
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    VPRINTF(LOW, "==========================================\n");
    VPRINTF(LOW, "After after reset and DAI idle:\n");
    VPRINTF(LOW, "==========================================\n");

    // Step 3 - tries writing and reading and checking a DAI error is returned
    for (uint32_t partition_no = CPTRA_SS_LOCK_HEK_PROD_0; partition_no <= CPTRA_SS_LOCK_HEK_PROD_7; partition_no++) {
      if (write_read_entire_partition(partition_no, w_data[0], w_data[1], OTP_CTRL_STATUS_DAI_ERROR_MASK, 0) == false) {
        goto epilogue;
      }
    }

    // zeroize all the HEK partitions:
    VPRINTF(LOW, "==========================================\n");
    VPRINTF(LOW, "Zeroizing all the fuses and markers for HEK partitions:\n");
    VPRINTF(LOW, "==========================================\n");


    // Step 4 - zeroize all the HEK fuses and markers

    for (uint32_t partition_no = CPTRA_SS_LOCK_HEK_PROD_0; partition_no <= CPTRA_SS_LOCK_HEK_PROD_7; partition_no++) {
      if(zeroize_all_partition(partition_no) == false) {
        goto epilogue;
      }
    }

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
    ratchet_seed_write_read();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
