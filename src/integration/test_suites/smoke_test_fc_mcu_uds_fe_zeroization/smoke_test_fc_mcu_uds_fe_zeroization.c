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
#include <stdint.h>

#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "fuse_ctrl_mmap.h"
#include "lc_ctrl.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"
#include "soc_ifc.h"

volatile char *stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

// This struct is used to store the partition information used in the test.
typedef struct partition_info {
  // Partition identifier. Used to access partition in the partitions array.
  uint32_t id;
  // Offset to the digest0 register.
  uint32_t digest0;
  // Offset to the digest1 register.
  uint32_t digest1;
} partition_info_t;

const partition_info_t kPartitionsInfo[] = {
    {
        .id = SECRET_MANUF_PARTITION,
        .digest0 = SOC_OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_1,
    },
    {
        .id = SECRET_PROD_PARTITION_0,
        .digest0 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_1,
    },
    {
        .id = SECRET_PROD_PARTITION_1,
        .digest0 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_DIGEST_1,
    },
    {
        .id = SECRET_PROD_PARTITION_2,
        .digest0 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_DIGEST_0,

        .digest1 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_DIGEST_1,
    },
    {
        .id = SECRET_PROD_PARTITION_3,
        .digest0 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_DIGEST_1,
    },
};
const uint32_t kNumPartitions =
    sizeof(kPartitionsInfo) / sizeof(kPartitionsInfo[0]);

static bool zeroization_check_unfeasible(uint32_t partition_id) {
  partition_t *p = &partitions[partition_id];
  uint32_t read_data[2];

  if (p->zer_address == 0) {
    VPRINTF(LOW, "MCU ERROR: Partition %d is not zeroizable\n", partition_id);
    return false;
  }

  // Read the digest to determine if the partition is locked
  dai_rd(p->digest_address, &read_data[0], &read_data[1], 64, 0);
  if (read_data[0] == 0 && read_data[1] == 0) {
    VPRINTF(LOW, "MCU ERROR: Partition %d is not locked\n", partition_id);
    return false;
  }

  // Check that the partition has not been zeroized already.
  dai_rd(p->zer_address, &read_data[0], &read_data[1], 64, 0);
  if (read_data[0] == 0xFFFFFFFF || read_data[1] == 0xFFFFFFFF) {
    VPRINTF(LOW, "MCU ERROR: Partition %d has already been zeroized\n", partition_id);
    return false;
  }

  // Attempt to zeroize. We check sure that the zeroize flag is still 0
  // to confirm that zeroization is not feasible from MCU.
  dai_zer(p->zer_address, &read_data[0], &read_data[1], 64,
          OTP_CTRL_STATUS_DAI_ERROR_MASK);
  if (read_data[0] != 0 || read_data[1] != 0) {
    VPRINTF(LOW, "MCU ERROR: Zeroize flag was set to 0x%x%x\n", read_data[1], read_data[0]);
    return false;
  }

  reset_fc_lcc_rtl();
  wait_dai_op_idle(0);

  return true;
}

// Check that the digest is zeroized or not.
static bool check_digest(uint32_t partition_id, bool expected_zeroized) {
  uint32_t digest[2];
  digest[0] = lsu_read_32(kPartitionsInfo[partition_id].digest0);
  digest[1] = lsu_read_32(kPartitionsInfo[partition_id].digest1);
  if (expected_zeroized) {
    return digest[0] == UINT32_MAX && digest[1] == UINT32_MAX;
  }
  // If not zeroized, the digest should not be all ones.
  return digest[0] != UINT32_MAX && digest[1] != UINT32_MAX;
}

static bool mcu_zeroization_test(void) {
  for (uint32_t i = 0; i < kNumPartitions; i++) {
    uint32_t partition_id = kPartitionsInfo[i].id;
    if (!zeroization_check_unfeasible(partition_id)) {
      VPRINTF(LOW,
              "MCU ERROR: Unexpected zeroization success for partition %d from MCU: "
              "PPD not set\n",
              partition_id);
      return false;
    }

    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FC_FORCE_ZEROIZATION);
    wait_dai_op_idle(0);

    if (!zeroization_check_unfeasible(partition_id)) {
      VPRINTF(LOW,
              "MCU ERROR: Unexpected zeroization success for partition %d from MCU: "
              "PPD not set\n",
              partition_id);
      return false;
    }

    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_RELEASE_ZEROIZATION);
    wait_dai_op_idle(0);
  }
  return true;
}

bool test(void) {
  VPRINTF(LOW, "@@@ Step 1/5: Initializing OTP controller 1/2\n");
  if (!wait_dai_op_idle(0)) return false;
  initialize_otp_controller();

  VPRINTF(LOW, "@@@ Step 2/5: Initializing OTP controller 2/2\n");
  if (!wait_dai_op_idle(0)) return false;
  initialize_otp_controller();

  // Before releasing Caliptra core, test that we are unable to zeroize any of
  // the partitions with or without PPD set.
  VPRINTF(LOW, "@@@ Step 3/5: Running zeroization test\n");
  if (!mcu_zeroization_test()) {
    VPRINTF(LOW, "MCU ERROR: Zeroization test failed\n");
    return false;
  }

  // Reset.
  VPRINTF(LOW, "@@@ Step 4/5: Applying reset\n");
  reset_fc_lcc_rtl();
  if (!wait_dai_op_idle(0)) return false;

  // At this point, the partitions should not be zeroized.
  VPRINTF(LOW, "@@@ Step 5/5: Checking partitions not zeroized\n");
  for (uint32_t i = 0; i < kNumPartitions; i++) {
    uint32_t partition_id = kPartitionsInfo[i].id;
    if (!check_digest(partition_id, /*expected_zeroized=*/false)) {
      VPRINTF(LOW, "MCU ERROR: Partition %d unexpectedly zeroized\n", kPartitionsInfo[i].id);
      return false;
    }
  }

  return true;
}

void main(void) {
  mcu_cptra_init_d();

  VPRINTF(LOW, "=====================================\n"
               "MCU Caliptra Boot Go\n"
               "=====================================\n\n");

  test();

  for (uint8_t ii = 0; ii < 160; ii++) {
    // Sleep loop as "nop".
    __asm__ volatile("nop");
  }
  SEND_STDOUT_CTRL(0xff);
}
