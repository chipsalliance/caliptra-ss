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
 * Program a LCC transition token in `VENDOR_SECRET_PROD_PARTITION` zeroize the secret
 * partition and verify that the valid bit is asserted once the partition has been locked.
 * The test proceeds in the following steps:
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
 *   9. Apply zeroization
 *   10.Verify the valid signal drops via SVA.
 */


void secret_partition_zeroization(void) {
  const uint32_t base_address = partitions[VENDOR_SECRET_PROD_PARTITION].address;
  const uint32_t fuse_address = base_address;//CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN;

  const uint32_t data[4] = {0xdeadbeef, 0xcafebabe, 0x12345678, 0xabababab};
  uint32_t read_data[4];
  uint32_t zero_r_data[2];
  uint32_t zeroize_num_times = 3;

  // Step 1. Write a full transition token into the partition.
  dai_wr(fuse_address, data[0], data[1], 64, 0);
  dai_wr(fuse_address+8, data[2], data[3], 64, 0);


  // Step 2. Read back the token and verify it is equal to the token written in Step 1.
  //         This works as long as the secret partition has not been locked.
  dai_rd(fuse_address, &read_data[0], &read_data[1], 64, 0);
  dai_rd(fuse_address+8, &read_data[2], &read_data[3], 64, 0);
  for (uint32_t idx = 0; idx < 4; idx++) {
    if (data[idx] != read_data[idx]) {
      VPRINTF(LOW, "ERROR: incorrect fuse data[index=%0d]: expected: %08X actual: %08X\n", idx, data[idx], read_data[idx]);
      goto epilogue;
    }
  }

  // Step 3. Verify that the partition's digest register is 0.
  uint32_t digest[2];
  digest[0] = lsu_read_32(SOC_OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_0);
  VPRINTF(LOW, "Afte step3\n");
  digest[1] = lsu_read_32(SOC_OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_1);
  if (digest[0] != 0 || digest[1] != 0) {
    VPRINTF(LOW, "ERROR: digest is not 0\n");
    goto epilogue;
  }

  // Step 4. Lock the partition by calculating a hardware digest.
  calculate_digest(base_address, 0);

  // Step 5. Reset the RTL.
  reset_fc_lcc_rtl();
  wait_dai_op_idle(0);

  // Step 6. Try to read the token and verify that it results in an error as the
  //         partition is secret and locked, thus not accessible by software anymore.
  dai_rd(fuse_address, &read_data[0], &read_data[1], 64, OTP_CTRL_STATUS_DAI_ERROR_MASK);

  // Step 7. Try to write a value into the partition and verify that it results in an error
  //         as the partition has been locked in Step 5.
  dai_wr(fuse_address, data[0], data[1], 64, OTP_CTRL_STATUS_DAI_ERROR_MASK);

  // Step 8. Read back the digest from the partition's digest register and verify it
  //         is non-zero.
  digest[0] = lsu_read_32(SOC_OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_0);
  digest[1] = lsu_read_32(SOC_OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_1);
  if (digest[0] == 0 || digest[1] == 0) {
    VPRINTF(LOW, "ERROR: digest is 0 - digest[0]=%0d, digest[1]=%0d\n", digest[0], digest[1]);
    goto epilogue;
  }

  // Step 9. Apply zeroization multiple_times
  for(uint32_t num_times = 0; num_times < zeroize_num_times; num_times++) {
    // Zeroize fuse.
    for (uint32_t addr = partitions[VENDOR_SECRET_PROD_PARTITION].address; addr < partitions[VENDOR_SECRET_PROD_PARTITION].digest_address; addr += (partitions[VENDOR_SECRET_PROD_PARTITION].granularity / 8)) {
      dai_zer(addr, &read_data[0], &read_data[1], partitions[VENDOR_SECRET_PROD_PARTITION].granularity, 0);
      if (read_data[0] != 0xFFFFFFFF || (partitions[VENDOR_SECRET_PROD_PARTITION].granularity> 32 && read_data[1] != 0xFFFFFFFF)) {
        VPRINTF(LOW, "ERROR: [partitions[SECRET_LC_TRANSITION_PARTITION] ]fuse is not zeroized\n");
        goto epilogue;
      }
    }
    memset(read_data, 0, sizeof(read_data));
    // Zeroize marker field.
    dai_zer(partitions[VENDOR_SECRET_PROD_PARTITION].zer_address, &read_data[0], &read_data[1], 64, 0);
    if (read_data[0] != 0xFFFFFFFF || read_data[1] != 0xFFFFFFFF) {
      VPRINTF(LOW, "ERROR: [partitions[VENDOR_SECRET_PROD_PARTITION] marker is not zeroized\n");
      goto epilogue;
    }
    memset(read_data, 0, sizeof(read_data));
    // Zeroize digest field.
    dai_zer(partitions[VENDOR_SECRET_PROD_PARTITION].digest_address, &read_data[0], &read_data[1], 64, 0);
    if (read_data[0] != 0xFFFFFFFF || read_data[1] != 0xFFFFFFFF) {
      VPRINTF(LOW, "ERROR: [partitions[VENDOR_SECRET_PROD_PARTITION] digest is not zeroized\n");
      goto epilogue;
    }
    memset(read_data, 0, sizeof(read_data));
  }

 epilogue:
  VPRINTF(LOW, "secret_partition_zeroization test finished\n");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    lcc_initialization();
    grant_mcu_for_fc_writes();


    // transition_state_check(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);

    initialize_otp_controller();
    VPRINTF(LOW, "=================\nSecret_partition_zeroization\n=================\n\n");
    secret_partition_zeroization();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
