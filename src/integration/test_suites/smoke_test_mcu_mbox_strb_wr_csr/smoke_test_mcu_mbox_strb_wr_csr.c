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

    uint32_t mci_boot_fsm_go;
    uint32_t mbox_num = decode_single_valid_mbox();
    uint32_t mask;

    mcu_cptra_init_d();

    ////////////////////////////////////
    // Mailbox command test
    //

    // MBOX: clear the lock on MBOX that is there from reset
    mcu_mbox_clear_lock_out_of_reset(mbox_num);

    VPRINTF(LOW, "=================\nMCU MBOX%x CSR STRBW Test\n=================\n\n", mbox_num)

    // MBOX: Acquire lock
    mcu_mbox_acquire_lock(mbox_num, 1000);


    // MBOX: Write and check STRBWs of DLEN
    mask = 0;
    for (uint32_t ii = 0; ii < 4; ii++) {
        VPRINTF(LOW, "MCU: Mbox%x write DLEN with STRBW byte: 0x%x\n", mbox_num, ii);
        lsu_write_8(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + ii + MCU_MBOX_NUM_STRIDE * mbox_num, 0xFF);

        VPRINTF(LOW, "MCU: Mbox%x Check DLEN\n", mbox_num);
        mask |= (0xFF << (ii * 8));
        if(mcu_mbox_read_dlen(mbox_num) != mask) {
            VPRINTF(FATAL, "MCU: Mbox%x DLEN CSR STRBW did not work for byte: %x\n", mbox_num, ii);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }

    // MBOX: Write execute with STRBW
    VPRINTF(LOW, "MCU: Mbox%x write execute\n", mbox_num);
    lsu_write_8(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, MCU_MBOX0_CSR_MBOX_EXECUTE_EXECUTE_MASK);

    VPRINTF(LOW, "MCU: Mbox%x Check Execute\n", mbox_num);
    // Check execute
    if (lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num) != 0x1) {
        VPRINTF(FATAL, "MCU: Mbox%x execute not set\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // MBOX: Write and check CMD with STRBW
    mask = 0;
    for (uint32_t ii = 0; ii < 4; ii++) {
        VPRINTF(LOW, "MCU: Mbox%x write CMD with STRBW byte: 0x%x\n", mbox_num, ii);
        lsu_write_8(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + ii + MCU_MBOX_NUM_STRIDE * mbox_num, 0xFF);

        VPRINTF(LOW, "MCU: Mbox%x check CMD\n", mbox_num);
        mask |= (0xFF << (ii * 8));
        if(mcu_mbox_read_cmd(mbox_num) != mask) {
            VPRINTF(FATAL, "MCU: Mbox%x CMD CSR STRBW did not work for byte: %x\n", mbox_num, ii);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }

    // MBOX: Write and check CMD_STATUS with STRBW
    VPRINTF(LOW, "MCU: Mbox%x write CMD status with STRBW\n", mbox_num);
    lsu_write_8(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, MCU_MBOX_DATA_READY);

    VPRINTF(LOW, "MCU: Mbox%x Check CMD_STATUS\n", mbox_num);
    if (lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num) != MCU_MBOX_DATA_READY) {
        VPRINTF(FATAL, "MCU: Mbox%x CMD_STATUS not written properly with STRBW\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // MBOX: Write and check TARGET_USER_VALID with STRBW
    VPRINTF(LOW, "MCU: Mbox%x write TARGET_USER_VALID with STRBW\n", mbox_num);
    lsu_write_8(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID + MCU_MBOX_NUM_STRIDE * mbox_num, 0x1);

    if (mcu_mbox_read_target_user_valid(mbox_num) != 0x1) {
        VPRINTF(FATAL, "MCU: Mbox%x TARGET_USER_VALID not written properly with STRBW\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // MBOX: Write and check TARGET_STATUS with STRBW
    VPRINTF(LOW, "MCU: Mbox%x write TARGET_STATUS with STRBW\n", mbox_num);
    lsu_write_8(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, 0x3);

    if (mcu_mbox_read_target_status(mbox_num) != 0x3) {
        VPRINTF(FATAL, "MCU: Mbox%x TARGET_STATUS not written properly with STRBW\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // MBOX: Write and check TARGET_USER with STRBW
    mask = 0;
    for (uint32_t ii = 0; ii < 4; ii++) {
        VPRINTF(LOW, "MCU: Mbox%x write TARGET_USER with STRBW byte: 0x%x\n", mbox_num, ii);
        lsu_write_8(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER + ii + MCU_MBOX_NUM_STRIDE * mbox_num, 0xFF);

        VPRINTF(LOW, "MCU: Mbox%x check CMD\n", mbox_num);
        mask |= (0xFF << (ii * 8));
        if(mcu_mbox_read_target_user(mbox_num) != mask) {
            VPRINTF(FATAL, "MCU: Mbox%x TARGET_USER CSR STRBW did not work for byte: %x\n", mbox_num, ii);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }

    SEND_STDOUT_CTRL(0xff);
}
