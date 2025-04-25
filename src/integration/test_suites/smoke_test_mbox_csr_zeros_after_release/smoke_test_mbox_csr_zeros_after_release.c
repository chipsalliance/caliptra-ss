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

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include <string.h>
#include <stdint.h>

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


void main (void) {
    int argc=0;
    char *argv[1];
    enum boot_fsm_state_e boot_fsm_ps;

    uint32_t mbox_resp_dlen;
    uint32_t mbox_resp_data;
    uint32_t mci_boot_fsm_go;
    uint32_t sram_data;
    uint32_t mbox_num = decode_single_valid_mbox();

    ////////////////////////////////////
    // Mailbox command test
    //
    VPRINTF(LOW, "=================\nMCU MBOX%x CSR Testing\n=================\n\n", mbox_num)

    // MBOX: Confim MCU already has lock out of reset
    if((lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK + MCU_MBOX_NUM_STRIDE * mbox_num) & MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK) == 0) {
        VPRINTF(FATAL, "MCU: Mbox%x lock should already be locked\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    uint32_t mbox_dlen = 64;
    uint32_t mbox_target_user = 8;
    uint32_t mbox_target_user_valid = 1;
    uint32_t mbox_cmd = 0xdead;
    uint32_t mbox_target_status = 0x2;
    uint32_t mbox_cmd_status = 0x1;

    // Write CSRs
    VPRINTF(LOW, "MCU: Mbox%x writing CSRs\n", mbox_num);
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num, mbox_dlen);

    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER + MCU_MBOX_NUM_STRIDE * mbox_num, mbox_target_user);

    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID + MCU_MBOX_NUM_STRIDE * mbox_num, mbox_target_user_valid);

    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + MCU_MBOX_NUM_STRIDE * mbox_num, mbox_cmd);
    
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, mbox_target_status);

    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, mbox_cmd_status);

    // MBOX: Confirm CSRs writes took affect
    if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num) != mbox_dlen) {
        VPRINTF(FATAL, "MCU: Mbox%x DLEN write failed\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER + MCU_MBOX_NUM_STRIDE * mbox_num) != mbox_target_user) {
        VPRINTF(FATAL, "MCU: Mbox%x Target User write failed\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID + MCU_MBOX_NUM_STRIDE * mbox_num) != mbox_target_user_valid) {
        VPRINTF(FATAL, "MCU: Mbox%x Target User Valid write failed\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + MCU_MBOX_NUM_STRIDE * mbox_num) != mbox_cmd) {
        VPRINTF(FATAL, "MCU: Mbox%x Target User Valid write failed\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num) != mbox_target_status) {
        VPRINTF(FATAL, "MCU: Mbox%x Target User Valid write failed\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num) != mbox_cmd_status) {
        VPRINTF(FATAL, "MCU: Mbox%x Target User Valid write failed\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // MBOX: Execute
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, MCU_MBOX0_CSR_MBOX_EXECUTE_EXECUTE_MASK);
    VPRINTF(LOW, "MCU: Mbox%x execute\n", mbox_num);

    // MBOX: Clear Execute
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, 0);
    VPRINTF(LOW, "MCU: Mbox%x execute clear\n", mbox_num);

    // MBOX: Confirm CSRs are 0 after execute clear
    if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num) != 0) {
        VPRINTF(FATAL, "MCU: Mbox%x DLEN should be 0\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num) != 0) {
        VPRINTF(FATAL, "MCU: Mbox%x Mbox User should be 0\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER + MCU_MBOX_NUM_STRIDE * mbox_num) != 0) {
        VPRINTF(FATAL, "MCU: Mbox%x Target User should be 0\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID + MCU_MBOX_NUM_STRIDE * mbox_num) != 0) {
        VPRINTF(FATAL, "MCU: Mbox%x Target User Valid should be 0\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + MCU_MBOX_NUM_STRIDE * mbox_num) != 0) {
        VPRINTF(FATAL, "MCU: Mbox%x Target User Valid should be 0\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num) != 0) {
        VPRINTF(FATAL, "MCU: Mbox%x Target User Valid should be 0\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num) != 0) {
        VPRINTF(FATAL, "MCU: Mbox%x Target User Valid should be 0\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    VPRINTF(LOW, "MCU: Mbox%x CRS are cleared\n", mbox_num);

    SEND_STDOUT_CTRL(0xff);
}
