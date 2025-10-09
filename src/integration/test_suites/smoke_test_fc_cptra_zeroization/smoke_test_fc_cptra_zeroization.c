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

void main(void) {
  VPRINTF(LOW, "=====================================\n"
               "MCU Caliptra Boot Go\n"
               "=====================================\n\n");

  // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring
  // Caliptra out of reset This is just to see CSSBootFSM running correctly
  mcu_mci_boot_go();

  // Wait for ready_for_fuses
  while (!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) &
           SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK))
    ;

  mcu_cptra_init_d(.cfg_skip_set_fuse_done = true);
  wait_dai_op_idle(0);
  initialize_otp_controller();

  // Emulate PPD to allow zeroization from Caliptra.
  lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FC_FORCE_ZEROIZATION);
  wait_dai_op_idle(0);

  // Releases the Caliptra core by setting CPTRA_FUSE_WR_DONE.
  lsu_write_32(SOC_SOC_IFC_REG_CPTRA_FUSE_WR_DONE,
               SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
  VPRINTF(LOW, "MCU: Set FUSE_WR_DONE\n");

  mcu_cptra_advance_brkpoint();

  // Enable ss_soc_dft_en_mask_reg
  lsu_write_32(SOC_MCI_TOP_MCI_REG_SOC_DFT_EN_0, 0x1);
  lsu_write_32(SOC_MCI_TOP_MCI_REG_SOC_HW_DEBUG_EN_0, 0x1);
  VPRINTF(LOW, "MCU: Set 0x1 to ss_soc_dft_en_mask_reg\n");
  VPRINTF(LOW, "MCU: Set 0x1 to ss_soc_hardware_dbg_en_mask_reg\n");

  uint32_t cptra_boot_go = 0;
  VPRINTF(LOW, "MCU: waits in success loop\n");

  // Wait for Caliptra to complete zeroization.
  while (cptra_boot_go !=
         SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_MASK) {
    cptra_boot_go =
        lsu_read_32(SOC_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP) &
        SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_MASK;
    for (uint32_t ii = 0; ii < 500; ii++) {
      __asm__ volatile("nop"); // Sleep loop as "nop"
    }
  }
  VPRINTF(LOW, "MCU: Success done\n");

  reset_fc_lcc_rtl();
  wait_dai_op_idle(0);

  // At this point, the partitions should be zeroized.
  for (uint32_t i = 0; i < kNumPartitions; i++) {
    if (!check_digest(&kPartitionsInfo[i], /*expected_zeroized=*/true)) {
      VPRINTF(LOW, "MCU ERROR: Partition %d is not zeroized\n", kPartitionsInfo[i].id);
      break;
    }
  }

  for (uint8_t ii = 0; ii < 160; ii++) {
    // Sleep loop as "nop".
    __asm__ volatile("nop");
  }
  SEND_STDOUT_CTRL(0xff);
}
