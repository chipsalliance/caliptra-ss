//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
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
// Description: MCU FW acting as Image Provider for 3-image AXI bypass
//              recovery flow per axi_recovery_flow.md.
//
// Image sizes:
//   Stage 0: 8 bytes   (2 DWORDs)
//   Stage 1: 512 bytes (128 DWORDs)
//   Stage 2: 516 bytes (129 DWORDs)
//********************************************************************************

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "string.h"
#include "stdint.h"
#include "veer-csr.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

#define NUM_STAGES 3
#define FIFO_DEPTH_DWORDS 64

// Image sizes in DWORDs for each stage
static const uint32_t img_size_dwords[NUM_STAGES] = { 2, 128, 129 };

// Poll DEVICE_STATUS_0.DEV_STATUS until it equals expected value
static void poll_dev_status(uint32_t expected, const char *desc) {
    uint32_t val;
    for (int i = 0; i < 500; i++) {
        val = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0)
              & I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0_DEV_STATUS_MASK;
        if (val == expected) {
            VPRINTF(LOW, "MCU: DEV_STATUS == 0x%x (%s)\n", expected, desc);
            return;
        }
        mcu_sleep(50);
    }
    handle_error("MCU: DEV_STATUS timeout waiting for 0x%x (%s), got 0x%x",
                 expected, desc, val);
}

// Poll RECOVERY_STATUS.DEV_REC_STATUS until it equals expected value
// and verify REC_IMG_INDEX matches expected_idx
static void poll_rec_status_awaiting(uint32_t expected_idx) {
    uint32_t raw, status, idx;
    for (int i = 0; i < 500; i++) {
        raw = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS);
        status = raw & I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS_DEV_REC_STATUS_MASK;
        if (status == 0x1) {
            idx = (raw & I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS_REC_IMG_INDEX_MASK)
                  >> I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS_REC_IMG_INDEX_LOW;
            VPRINTF(LOW, "MCU: DEV_REC_STATUS == 0x1, REC_IMG_INDEX == 0x%x\n", idx);
            if (idx != expected_idx) {
                handle_error("MCU: REC_IMG_INDEX mismatch: expected 0x%x got 0x%x",
                             expected_idx, idx);
            }
            return;
        }
        mcu_sleep(50);
    }
    handle_error("MCU: DEV_REC_STATUS timeout waiting for 0x1, got 0x%x", status);
}

// Write data to FIFO in chunks of FIFO_DEPTH_DWORDS, polling EMPTY between
static void write_image_data(uint32_t stage, uint32_t num_dwords) {
    uint32_t written = 0;
    uint32_t fifo_status;

    while (written < num_dwords) {
        uint32_t chunk = num_dwords - written;
        if (chunk > FIFO_DEPTH_DWORDS) {
            chunk = FIFO_DEPTH_DWORDS;
        }

        VPRINTF(LOW, "MCU: Stage %d: writing chunk of %d DWORDs (offset %d/%d)\n",
                stage, chunk, written, num_dwords);

        for (uint32_t j = 0; j < chunk; j++) {
            uint32_t data = (stage << 24) | (written + j);
            lsu_write_32(SOC_I3CCSR_I3C_EC_TTI_TX_DATA_PORT, data);
        }
        written += chunk;

        // If more data to send, poll FIFO empty before next chunk
        if (written < num_dwords) {
            for (int p = 0; p < 2000; p++) {
                fifo_status = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_0)
                              & I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_0_EMPTY_MASK;
                if (fifo_status) {
                    VPRINTF(LOW, "MCU: FIFO empty after chunk\n");
                    break;
                }
                mcu_sleep(10);
            }
            if (!fifo_status) {
                handle_error("MCU: FIFO not empty timeout after chunk at stage %d", stage);
            }
        }
    }
    VPRINTF(LOW, "MCU: Stage %d: all %d DWORDs written\n", stage, num_dwords);
}

// Wait for DEV_STATUS to change from 0x4, return new value
static uint32_t wait_for_stage_completion(void) {
    uint32_t val;
    for (int i = 0; i < 500; i++) {
        val = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0)
              & I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0_DEV_STATUS_MASK;
        if (val != 0x4) {
            VPRINTF(LOW, "MCU: DEV_STATUS changed from 0x4 to 0x%x\n", val);
            return val;
        }
        mcu_sleep(50);
    }
    handle_error("MCU: DEV_STATUS stuck at 0x4, timeout");
    return 0xF;
}


void main (void) {

    uint32_t i3c_reg_data;

    VPRINTF(LOW, "=== MCU boot.. started ==\n");

    // Set MCU SRAM exec region to 128KB (value 31, base-0, 32*4KB=128KB).
    // This ensures Caliptra DMA can write recovery images to MCU SRAM
    // without hitting the protected region filter.
    // Default exec region is only 4KB; offsets beyond 0x1000 are protected.
    mcu_cptra_init_d(
        .cfg_mcu_fw_sram_exec_reg_size = true,
        .mcu_fw_sram_exec_reg_size = 31,
        .cfg_enable_cptra_mbox_user_init = true,
        .cfg_cptra_fuse = true,
        .cfg_cptra_wdt = true);

    // Initialize I3C recovery registers only (PROT_CAP, DEVICE_ID, HW_STATUS).
    // Do NOT call boot_i3c_core() -- that enables the I3C bus which we don't want
    // in AXI bypass mode.
    boot_i3c_reg();

    // Enable AXI bypass mode (once, never cleared)
    i3c_reg_data = I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_CFG_REC_INTF_BYPASS_MASK;
    lsu_write_32(SOC_I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_CFG, i3c_reg_data);
    VPRINTF(LOW, "MCU: I3C BYPASS mode set\n");

    // Verify PROT_CAP_0/1, DEVICE_ID, HW_STATUS
    i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_0);
    if (i3c_reg_data != 0x2050434f) {
        handle_error("MCU: PROT_CAP_0 mismatch: expected 0x%x got 0x%x",
                     0x2050434f, i3c_reg_data);
    }
    i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_1);
    if (i3c_reg_data != 0x56434552) {
        handle_error("MCU: PROT_CAP_1 mismatch: expected 0x%x got 0x%x",
                     0x56434552, i3c_reg_data);
    }
    i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_0);
    if (i3c_reg_data != 1) {
        handle_error("MCU: DEVICE_ID_0 mismatch: expected 0x1 got 0x%x", i3c_reg_data);
    }
    i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS);
    if (i3c_reg_data != 0x00000100) {
        handle_error("MCU: HW_STATUS mismatch: expected 0x100 got 0x%x", i3c_reg_data);
    }

    VPRINTF(LOW, "=== MCU boot.. completed ==\n");

    //-- Multi-stage recovery loop (3 images)
    for (uint32_t stage = 0; stage < NUM_STAGES; stage++) {

        VPRINTF(LOW, "MCU: ========== Stage %d ==========\n", stage);

        // Step 5: Poll DEVICE_STATUS_0 until DEV_STATUS == 0x3
        poll_dev_status(0x3, "recovery mode ready");

        // Step 6: Poll RECOVERY_STATUS until DEV_REC_STATUS == 0x1
        //         and verify REC_IMG_INDEX matches stage
        poll_rec_status_awaiting(stage);

        // Step 7 is handled by the REC_PAYLOAD_DONE clear at step 18
        // (line after wait_for_stage_completion). For stage 0, it was
        // never set so no clear needed.

        // Step 8: Write IMAGE_SIZE to INDIRECT_FIFO_CTRL_1 (in 4B units)
        lsu_write_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_1,
                     img_size_dwords[stage]);
        VPRINTF(LOW, "MCU: IMAGE_SIZE set to 0x%x DWORDs\n", img_size_dwords[stage]);

        // Step 9: Data transfer loop
        write_image_data(stage, img_size_dwords[stage]);

        // Step 10: Set REC_PAYLOAD_DONE (keep BYPASS set)
        i3c_reg_data = I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_CFG_REC_INTF_BYPASS_MASK
                     | I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_CFG_REC_PAYLOAD_DONE_MASK;
        lsu_write_32(SOC_I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_CFG, i3c_reg_data);
        VPRINTF(LOW, "MCU: REC_PAYLOAD_DONE set\n");

        // Step 13: Poll DEVICE_STATUS_0 until DEV_STATUS == 0x4
        poll_dev_status(0x4, "recovery pending / awaiting activation");

        // Step 14: Write ACTIVATE_REC_IMG = 0xF via W1C sideband
        lsu_write_32(SOC_I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_REG_W1C_ACCESS,
                     0x0F << I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_REG_W1C_ACCESS_RECOVERY_CTRL_ACTIVATE_REC_IMG_LOW);
        VPRINTF(LOW, "MCU: ACTIVATE_REC_IMG = 0xF written\n");

        // Step 16/18: Wait for DEV_STATUS to change from 0x4
        uint32_t next_status = wait_for_stage_completion();

        // Clear REC_PAYLOAD_DONE immediately after stage completes to prevent
        // stale payload_available in the next stage. Caliptra polls
        // payload_available after writing RECOVERY_STATUS, so this must be
        // cleared before Caliptra enters the next stage.
        i3c_reg_data = I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_CFG_REC_INTF_BYPASS_MASK;
        lsu_write_32(SOC_I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_CFG, i3c_reg_data);
        VPRINTF(LOW, "MCU: REC_PAYLOAD_DONE cleared after stage completion\n");

        if (next_status == 0xF) {
            handle_error("MCU: Device FW reported error (DEV_STATUS=0xF) at stage %d", stage);
        }

        if (stage < NUM_STAGES - 1) {
            // Intermediate stage: expect DEV_STATUS == 0x3 (next stage ready)
            if (next_status != 0x3) {
                handle_error("MCU: Expected DEV_STATUS 0x3 for next stage, got 0x%x at stage %d",
                             next_status, stage);
            }
            VPRINTF(LOW, "MCU: Stage %d complete, proceeding to next stage\n", stage);
        } else {
            // Final stage: expect DEV_STATUS == 0x1 (device healthy)
            if (next_status != 0x1) {
                handle_error("MCU: Expected DEV_STATUS 0x1 (healthy) at final stage, got 0x%x",
                             next_status);
            }
            VPRINTF(LOW, "MCU: Final stage %d complete, recovery successful\n", stage);
        }
    }

    VPRINTF(LOW, "MCU: All %d stages complete. Test PASSED.\n", NUM_STAGES);

    // End test with success
    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    csr_write_mpmc_halt();
}
