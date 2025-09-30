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
#include <stddef.h>

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

// Check that the partition containing address is indeed secret by trying to read the address and
// checking we get a DAI_ERROR response and rdata of zero.
static bool check_secret_at(uint32_t address)
{
  uint32_t read_data[2];

  // Read the value at the address to determine if the partition is secret. If the partition is
  // secret, we should see a DAI_ERROR.
  if (!dai_rd(address, &read_data[0], &read_data[1], 64, OTP_CTRL_STATUS_DAI_ERROR_MASK)) {
    VPRINTF(LOW, "MCU ERROR: Didn't get expected DAI error when accessing %x\n", address);
    return false;
  }

  // What's more, we expect the rdata to be dead zero (rather than the partition giving us some
  // exciting data)
  if (read_data[0] != 0 || read_data[1] != 0) {
    VPRINTF(LOW, "MCU ERROR: Failing DaiRd operation returned nonzero data: {%x, %x}\n",
            read_data[0], read_data[1]);
    return false;
  }

  return true;
}

// Try to zeroize the given partition. This won't work, because the partition should be locked.
// Check that we get the sort of "access denied" behaviour we expect.
static bool zeroization_check_unfeasible(const partition_t *partition) {
  uint32_t read_data[2];

  if (partition->zer_address == 0) {
    VPRINTF(LOW, "MCU ERROR: Partition %d is not zeroizable\n", partition->index);
    return false;
  }

  // If this weren't a secret partition, we might look at the digest or the zeroization address to
  // figure out whether the partition had already been locked. Since it *is* a secret partition,
  // that won't actually work: we are the MCU and fuse_ctrl won't give us access to the partition.
  //
  // Check that the partition genuinely is inaccessible by trying (and failing) to read the digest
  // and from the zeroization address.
  if (!check_secret_at(partition->digest_address)) {
    VPRINTF(LOW, "MCU ERROR: Surprising access: digest of partition %d\n", partition->index);
    return false;
  }
  if (!check_secret_at(partition->zer_address)) {
    VPRINTF(LOW, "MCU ERROR: Surprising access: zer_address of partition %d\n", partition->index);
    return false;
  }

  // Attempt to zeroize, which should fail.
  if (!dai_zer(partition->zer_address, 64, OTP_CTRL_STATUS_DAI_ERROR_MASK, false))
      return false;

  reset_fc_lcc_rtl();
  return wait_dai_op_idle(0);
}

// Check that the digest is zeroized or not.
static bool check_digest(const partition_info_t *partition_info, bool expected_zeroized) {
  uint32_t digest[2];
  digest[0] = lsu_read_32(partition_info->digest0);
  digest[1] = lsu_read_32(partition_info->digest1);
  if (expected_zeroized) {
    return digest[0] == UINT32_MAX && digest[1] == UINT32_MAX;
  }
  // If not zeroized, the digest should not be all ones.
  return digest[0] != UINT32_MAX || digest[1] != UINT32_MAX;
}

static const partition_t *index_to_partition(uint32_t index)
{
  for (int i = 0; i < NUM_PARTITIONS; i++)
    if (partitions[i].index == index) return &partitions[i];

  VPRINTF(LOW, "MCU ERROR: Cannot find partition with index %d.\n", index);
  return NULL;
}

static bool mcu_zeroization_test(void) {
  for (uint32_t i = 0; i < kNumPartitions; i++) {
    const partition_t *partition = index_to_partition(kPartitionsInfo[i].id);
    if (!partition) return false;

    for (int j = 0; j < 2; j++) {
      if (!zeroization_check_unfeasible(partition)) {
        VPRINTF(LOW, "MCU ERROR: Unexpected zeroization result for partition %d from MCU.",
                partition->index);
        return false;
      }

      uint32_t cmd = (j == 0) ? CMD_FC_FORCE_ZEROIZATION : CMD_RELEASE_ZEROIZATION;

      lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, cmd);
      if (!wait_dai_op_idle(0)) return false;
    }
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
    if (!check_digest(&kPartitionsInfo[i], /*expected_zeroized=*/false)) {
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
