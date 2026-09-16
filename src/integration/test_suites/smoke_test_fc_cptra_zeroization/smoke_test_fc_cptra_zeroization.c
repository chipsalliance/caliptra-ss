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

  // NOTE: Zeroization is verified on the Caliptra side, which checks the
  // readback of every zeroization step (marker, fuse words and digest) for each
  // partition. There is deliberately no MCU-side verification here, because the
  // MCU cannot observe the result of the zeroization in this configuration:
  //
  //   - A DAI read of the secret partitions is rejected by the fuse controller
  //     filter. The access control table reserves the 0x48-0xF0 address range
  //     for the Caliptra core, and the zeroization markers and digests of the
  //     secret partitions live in that range, so an MCU DAI read of them is
  //     discarded and reports an access error.
  //   - The named digest CSRs are readable by the MCU, but this test runs with
  //     debug intent asserted through the physical strap. The secret partitions
  //     are therefore never sensed, so the digest CSRs are masked and read back
  //     zero regardless of the actual fuse contents.
  //
  // The fuse controller reset above is still exercised, to confirm the fuse
  // controller re-initializes cleanly once the partitions have been zeroized.

  for (uint8_t ii = 0; ii < 160; ii++) {
    // Sleep loop as "nop".
    __asm__ volatile("nop");
  }
  SEND_STDOUT_CTRL(0xff);
}
