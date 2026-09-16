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

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


void mcu_mbox_check_root_access(uint32_t mbox_num, uint32_t target_axi_user) {
    uint32_t mbox_data[] = { 0x00000000,
                            0x11111111,
                            0x22222222,
                            0x33333333,
                            0x44444444,
                            0x55555555,
                            0x66666666,
                            0x77777777,
                            0x88888888,
                            0x99999999,
                            0xaaaaaaaa,
                            0xbbbbbbbb,
                            0xcccccccc,
                            0xdddddddd,
                            0xeeeeeeee,
                            0xffffffff };

    uint32_t mbox_resp_data;
    const uint32_t mbox_dlen = sizeof(mbox_data);
    uint32_t test_data;
    uint32_t value_before;

    VPRINTF(LOW, "MCU: Mbox%x checking Root access while external Requester holds lock\n", mbox_num);

    if (mcu_mbox_read_sram_owner(mbox_num) != MCU_MBOX_SRAM_OWNER_ROOT) {
        VPRINTF(FATAL, "MCU: Mbox%x SRAM owner should be Root after Requester sets EXECUTE\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Root owns the response SRAM and DLEN while the command is BUSY.
    for (uint32_t ii = 0; ii < mbox_dlen/4; ii++) {
        VPRINTF(LOW, "MCU: Writing to MBOX%x data: 0x%x\n", mbox_num, mbox_data[ii]); 
        lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii) + MCU_MBOX_NUM_STRIDE * mbox_num, mbox_data[ii]);
    }

    for (uint32_t ii = 0; ii < mbox_dlen/4; ii++) {
        mbox_resp_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii) + MCU_MBOX_NUM_STRIDE * mbox_num);
        VPRINTF(LOW, "MCU: Reading data from MBOX%x SRAM: Data[%d] 0x%x\n", mbox_num, ii, mbox_resp_data);
        // Compare expected data
        if (mbox_resp_data != mbox_data[ii]) {
            VPRINTF(FATAL, "MCU: Wasn't able to write Mbox%x SRAM data while user locked - dword: %x expected data: %x\n", mbox_num, ii, mbox_data[ii]);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }

    VPRINTF(LOW, "MCU: Writing MBOX%x DLEN: 0x%x\n", mbox_num, mbox_dlen);
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num, mbox_dlen);

    if (lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num) != mbox_dlen) {
        VPRINTF(FATAL, "MCU: Wasn't able to write Mbox%x DLEN as Root\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // CMD and EXECUTE belong to the external Requester, not Root.
    value_before = mcu_mbox_read_cmd(mbox_num);
    mcu_mbox_write_cmd(mbox_num, ~value_before);
    if (mcu_mbox_read_cmd(mbox_num) != value_before) {
        VPRINTF(FATAL, "MCU: Mbox%x Root changed Requester-owned CMD\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    value_before = mcu_mbox_read_execute(mbox_num);
    mcu_mbox_clear_execute(mbox_num);
    if ((value_before != 1) || (mcu_mbox_read_execute(mbox_num) != value_before)) {
        VPRINTF(FATAL, "MCU: Mbox%x Root changed Requester-owned EXECUTE\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // USER, LOCK, and HW_STATUS are read-only.
    test_data = xorshift32();
    value_before = mcu_mbox_read_mbox_user(mbox_num);
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num, test_data);
    if (mcu_mbox_read_mbox_user(mbox_num) != value_before) {
        VPRINTF(FATAL, "MCU: Changed read-only Mbox%x USER\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    value_before = mcu_mbox_read_lock(mbox_num);
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK + MCU_MBOX_NUM_STRIDE * mbox_num, 0x0);
    if (mcu_mbox_read_lock(mbox_num) != value_before) {
        VPRINTF(FATAL, "MCU: Changed read-only Mbox%x LOCK\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    value_before = mcu_mbox_read_hw_status(mbox_num);
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_HW_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_SINGLE_ERROR_MASK | MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_DOUBLE_ERROR_MASK);
    if (mcu_mbox_read_hw_status(mbox_num) != value_before) {
        VPRINTF(FATAL, "MCU: Changed read-only Mbox%x HW_STATUS\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Root owns target configuration and CMD_STATUS.
    mcu_mbox_write_target_user(mbox_num, target_axi_user);
    if (mcu_mbox_read_target_user(mbox_num) != target_axi_user) {
        VPRINTF(FATAL, "MCU: Wasn't able to write Mbox%x TARGET_USER as Root\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    value_before = mcu_mbox_read_target_status(mbox_num);
    mcu_mbox_write_target_status(mbox_num, MCU_MBOX_TARGET_STATUS_FAILURE);
    if (mcu_mbox_read_target_status(mbox_num) != value_before) {
        VPRINTF(FATAL, "MCU: Mbox%x Root changed Target-owned TARGET_STATUS\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    mcu_mbox_write_target_user_valid(mbox_num, 1);
    if (mcu_mbox_read_target_user_valid(mbox_num) != 1) {
        VPRINTF(FATAL, "MCU: Wasn't able to write Mbox%x TARGET_USER_VALID as Root\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if (mcu_mbox_read_sram_owner(mbox_num) != MCU_MBOX_SRAM_OWNER_TARGET) {
        VPRINTF(FATAL, "MCU: Mbox%x SRAM owner should be Target after grant\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    mcu_mbox_write_cmd_status(mbox_num, MCU_MBOX_CMD_COMPLETE);
    if (mcu_mbox_read_cmd_status(mbox_num) != MCU_MBOX_CMD_COMPLETE) {
        VPRINTF(FATAL, "MCU: Wasn't able to write Mbox%x CMD_STATUS as Root\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if (mcu_mbox_read_sram_owner(mbox_num) != MCU_MBOX_SRAM_OWNER_TARGET) {
        VPRINTF(FATAL, "MCU: Mbox%x Root CMD_STATUS write stole ownership from Target\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}

// Test (in conjunction with Caliptra uC C code) checks MCU Root access while an
// external Requester holds the mailbox lock.
// 1. Caliptra uC acquires mailbox, writes data to SRAM, sets EXECUTE
// 2. MCU waits for execute
// 3. MCU verifies Root can write response SRAM/DLEN, target configuration, and
//    CMD_STATUS, but cannot write Requester-owned CMD/EXECUTE or TARGET_STATUS

void main (void) {
    int argc=0;
    char *argv[1];
    enum boot_fsm_state_e boot_fsm_ps;
    const uint32_t mbox_dlen = 16*4;
    uint32_t mbox_resp_dlen;
    uint32_t mbox_resp_data;
    uint32_t mci_boot_fsm_go;
    uint32_t sram_data;  
    uint32_t mbox_num = decode_single_valid_mbox();
    bool     mbox0_sel = true;
    uint32_t axi_select = xorshift32() % 5;

    uint32_t axi_user_id[] = { xorshift32(), xorshift32(), xorshift32(), xorshift32(), xorshift32() };
    VPRINTF(LOW, "MCU: Configured Valid AXI USERs: 0 - 0x%x; 1 - 0x%x; 2 - 0x%x; 3 - 0x%x; 4 - 0x%x;\n", axi_user_id[0], axi_user_id[1], axi_user_id[2], axi_user_id[3], axi_user_id[4]);
    
    uint32_t caliptra_uc_axi_id = axi_user_id[axi_select];
    VPRINTF(LOW, "MCU: Valid AXI USER for test AXI: 0x%x;\n", caliptra_uc_axi_id);

    VPRINTF(LOW, "MCU: Caliptra bringup\n");

    if(mbox_num) {
        mbox0_sel = false;
    }

    mcu_cptra_init_d(.cfg_cptra_dma_axi_user=true, .cptra_dma_axi_user=caliptra_uc_axi_id, .cfg_mcu_mbox0_valid_user=mbox0_sel, .mcu_mbox0_valid_user=axi_user_id, .cfg_mcu_mbox1_valid_user=!mbox0_sel, .mcu_mbox1_valid_user=axi_user_id);

    mcu_mbox_clear_lock_out_of_reset(mbox_num);

    ////////////////////////////////////
    // Mailbox command test
    ////////////////////////////////////

    // Wait for Caliptra Core to acquire lock, write MBOX data, and set execute
    // Do writes to SRAM and CSRs and verify that write occured with reads.
    if(!mcu_mbox_wait_for_user_lock(mbox_num, caliptra_uc_axi_id, 10000)) {
        VPRINTF(FATAL, "MCU: Mbox%x Caliptra did not acquire lock and set execute\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    if(!mcu_mbox_wait_for_user_execute(mbox_num, 1, 10000)) {
        VPRINTF(FATAL, "MCU: Mbox%x Caliptra did not set execute\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    
    mcu_mbox_check_root_access(mbox_num, caliptra_uc_axi_id);

    VPRINTF(LOW, "MCU: Sequence complete\n");

    SEND_STDOUT_CTRL(0xff);
}
