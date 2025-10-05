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




void volatile_lock_set_write_read_ratchet(uint32_t lock_value, uint32_t wdata0, uint32_t wdata1, uint32_t partition_locked) {
  uint32_t mask, partition_index_offset;
  uint32_t rdata[2];

  lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, lock_value);
  partition_index_offset = CPTRA_SS_LOCK_HEK_PROD_0;
  for (uint32_t partition_no = CPTRA_SS_LOCK_HEK_PROD_0; partition_no <= CPTRA_SS_LOCK_HEK_PROD_7; partition_no++) {
    mask = (((partition_no-partition_index_offset) < lock_value) ||  partition_locked) ? OTP_CTRL_STATUS_DAI_ERROR_MASK : 0;

    dai_wr(partitions[partition_no].address, wdata0, wdata1 , partitions[partition_no].granularity, mask);
    dai_rd(partitions[partition_no].address, &rdata[0],&rdata[1] , partitions[partition_no].granularity, 0);
    // Only compare when an error is not expected
    if (mask == 0 &&
        (wdata0 != rdata[0] || (partitions[partition_no].granularity > 32 && rdata[1] != wdata1))
        ) {
      VPRINTF(LOW, "ERROR: partitions[HEK_no=%0d] read_value, does not match written_value\n", partition_no);
      break;
    }
  }
}


/**
   This tests takes the following steps:
   1 - Write read each ratchet seed while testing all possible values of ratchet_seed_volatile_lock with the partition unlocked
   2 - calculates the digest, and resets the device
   3 - Writes read each ratchet seed now that partition is locked: all writes should fail
*/

void ratchet_seed_volatile_lock(void) {
  uint32_t data[2];
  uint32_t partition_locked = 0;

  VPRINTF(LOW, "==================================\n");
  VPRINTF(LOW, "testing all ratchet seed registers \n");
  VPRINTF(LOW, "==================================\n\n");

  // Step 1 - Write read each ratchet seed while testing all possible values of ratchet_seed_volatile_lock with the partition unlocked
  for (uint32_t lock_value = 0; lock_value <= 8; lock_value++) {
    volatile_lock_set_write_read_ratchet(lock_value, 0xFF, 0xFF, partition_locked);
  }


  VPRINTF(LOW, "==========================================\n");
  VPRINTF(LOW, "Before the digests have been calculated\n");
  VPRINTF(LOW, "==========================================\n");

  // Step 2 - calculates the digest for all HEKs - which locks the partition, and reset the device

  // First start by unsetting the lock, so the DAI writes can proceed
  lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0);
  for (uint32_t partition_no = CPTRA_SS_LOCK_HEK_PROD_0; partition_no <= CPTRA_SS_LOCK_HEK_PROD_7; partition_no++) {
    dai_wr(partitions[partition_no].digest_address, 0xFF, 0xFF, 32, 0);
  }
  partition_locked = 1;
  VPRINTF(LOW, "==========================================\n");
  VPRINTF(LOW, "All the digests for HEKs partitions have been calculated\n");
  VPRINTF(LOW, "==========================================\n");


  //=================================
  // Reset:
  //=================================
  reset_fc_lcc_rtl();
  wait_dai_op_idle(0);

  VPRINTF(LOW, "==========================================\n");
  VPRINTF(LOW, "After after reset and DAI idle:\n");
  VPRINTF(LOW, "==========================================\n");


  // Step 3 - Writes read each ratchet seed now that partition is locked: all writes should fail
  for (uint32_t lock_value = 0; lock_value <= 8; lock_value++) {
    volatile_lock_set_write_read_ratchet(lock_value, 0xFF, 0xFF, partition_locked);
  }


  VPRINTF(LOW, "Ratchet seed volatile lock test finished\n");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    initialize_otp_controller();

    VPRINTF(LOW, "=================\nBefore ratchet_seed_volatile_lock\n=================\n\n");
    ratchet_seed_volatile_lock();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
