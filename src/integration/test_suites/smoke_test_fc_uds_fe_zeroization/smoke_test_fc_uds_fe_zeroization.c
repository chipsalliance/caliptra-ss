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

volatile char* stdout = (char*)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

#define LOG_ERROR(...) VPRINTF(LOW, "MCU ERROR:" #__VA_ARGS__)
#define LOG_INFO(...) VPRINTF(LOW, "MCU:" #__VA_ARGS__)

const uint32_t kPartitions[] = {
  SECRET_MANUF_PARTITION//,
  // SECRET_PROD_PARTITION_0,
  // SECRET_PROD_PARTITION_1,
  // SECRET_PROD_PARTITION_2,
  // SECRET_PROD_PARTITION_3,
};
const uint32_t kNumPartitions = sizeof(kPartitions) / sizeof(kPartitions[0]);

static bool zeroization_check_unfeasible(uint32_t partition_id) {
  partition_t *p = &partitions[partition_id];
  uint32_t read_data[2];

  if (p->zer_address == 0) {
    LOG_ERROR("Partition %d is not zeroizable\n", partition_id);
    return false;
  }

  // Read the digest to determine if the partition is locked
  dai_rd(p->digest_address, &read_data[0], &read_data[1], 64, 0);
  if (read_data[0] == 0 && read_data[1] == 0) {
    LOG_ERROR("Partition %d is not locked\n", partition_id);
    return false;
  }

  // Check that the partition has not been zeroized already.
  dai_rd(p->zer_address, &read_data[0], &read_data[1], 64, 0);
  if (read_data[0] == 0xFFFFFFFF || read_data[1] == 0xFFFFFFFF) {
    LOG_ERROR("Partition %d has already been zeroized\n", partition_id);
    return false;
  }

  // Attempt to zeroize. We check sure that the zeroize flag is still 0
  // to confirm that zeroization is not feasible from MCU.
  dai_zer(p->zer_address, &read_data[0], &read_data[1], 64, OTP_CTRL_STATUS_DAI_ERROR_MASK);
  if (read_data[0] != 0 || read_data[1] != 0) {
    LOG_ERROR("Zeroize flag was set to 0x%x%x\n", read_data[1], read_data[0]);
    return false;
  }

  reset_fc_lcc_rtl();
  wait_dai_op_idle(0);

  return true;
}

static bool zeroization_caliptra_request(uint32_t partition_id) {
  // Configure the partition ID.
  lsu_write_32(SOC_SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_L, partition_id);

  // Error if there is already a request in progress, otherwise request
  // zeroization.
  uint32_t reg = lsu_read_32(SOC_SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ);
  if (reg & SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_UDS_PROGRAM_REQ_MASK) {
    LOG_ERROR("Zeroization request already in progress\n");
    return false;
  }
  lsu_write_32(SOC_SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ,
               reg | SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_UDS_PROGRAM_REQ_MASK);

  // Poll for completion.
  while (lsu_read_32(SOC_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP) &
         SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_MASK);

  reg = lsu_read_32(SOC_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP);
  if (reg & SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK) {
    return true;
  }
  reset_fc_lcc_rtl();
  wait_dai_op_idle(0);


  return false;
}

void main(void) {
  VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")

  // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring
  // Caliptra out of reset This is just to see CSSBootFSM running correctly
  mcu_mci_boot_go();

  // Wait for ready_for_fuses
  while (!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) &
           SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK));

  mcu_cptra_init_d(.cfg_skip_set_fuse_done = true);
  wait_dai_op_idle(0);
  initialize_otp_controller();

  // Grant permission to perform writes even though we are expecting the
  // operation to fail.
  // grant_mcu_for_fc_writes();

  // Before releasing Caliptra core, test that we are unable to zeroize any of
  // the partitions with or without PPD set.
  for (uint32_t i = 0; i < kNumPartitions; i++) {
    uint32_t partition_id = kPartitions[i];
    if (!zeroization_check_unfeasible(partition_id)) {
      LOG_ERROR(
          "Unexpected zeroization success for partition_id: %d from MCU - PPD "
          "not set\n",
          partition_id);
      goto epilog;
    }

    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FC_FORCE_ZEROIZATION);
    wait_dai_op_idle(0);

    if (!zeroization_check_unfeasible(partition_id)) {
      LOG_ERROR(
          "Unexpected zeroization success for partition_id: %d from MCU - PPD "
          "set\n",
          partition_id);
      goto epilog;
    }

    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_RELEASE_ZEROIZATION);
    wait_dai_op_idle(0);
  }

  // revoke_grant_mcu_for_fc_writes();

  // Releases the Caliptra core by setting CPTRA_FUSE_WR_DONE.
  lsu_write_32(SOC_SOC_IFC_REG_CPTRA_FUSE_WR_DONE,
               SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
  LOG_INFO("Set FUSE_WR_DONE\n");


  // grant_caliptra_core_for_fc_writes();

  // Expect zeroization to FAIL when PPD IS NOT set.
  for (uint32_t i = 0; i < kNumPartitions; i++) {
    uint32_t partition_id = kPartitions[i];
    if (zeroization_caliptra_request(partition_id)) {
      LOG_ERROR(
          "Unexpected zeroization success for partition_id: %d from Caliptra - "
          "PPD not set\n",
          partition_id);
      goto epilog;
    }
  }

  lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FC_FORCE_ZEROIZATION);
  wait_dai_op_idle(0);

  // Expect zeroization to PASS after PPD IS set.
  for (uint32_t i = 0; i < kNumPartitions; i++) {
    uint32_t partition_id = kPartitions[i];
    if (!zeroization_caliptra_request(partition_id)) {
      LOG_ERROR(
          "Unexpected zeroization failure for partition_id: %d from Caliptra - "
          "PPD set\n",
          partition_id);
      goto epilog;
    }
  }

  lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_RELEASE_ZEROIZATION);
  wait_dai_op_idle(0);

  // revoke_grant_mcu_for_fc_writes();

  // TODO(moidx): Should we issue reset and verify that the partitions are
  // zeroized?

epilog:
  for (uint8_t ii = 0; ii < 160; ii++) {
    // Sleep loop as "nop".
    __asm__ volatile("nop");
  }
  SEND_STDOUT_CTRL(0xff);
}
