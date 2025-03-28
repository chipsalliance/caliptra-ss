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


void mcu_mbox0_write_sram_and_csrs(){
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
    uint32_t mbox_dlen;

    // Do SRAM and CSRs write while user has lock
    //// MBOX: Write data
    for (uint32_t ii = 0; ii < mbox_dlen/4; ii++) {
        VPRINTF(LOW, "MCU: Writing to MBOX data: 0x%x\n", mbox_data[ii]); 
        lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii), mbox_data[ii]);
    }

    for (uint32_t ii = 0; ii < mbox_dlen/4; ii++) {
        mbox_resp_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii));
        VPRINTF(LOW, "MCU: Reading data from MBOX SRAM: Data[%d] 0x%x\n", ii, mbox_resp_data);
        // Compare expected data
        if (mbox_resp_data != mbox_data[ii]) {
            VPRINTF(FATAL, "MCU: Wasn't able to write Mbox0 SRAM data while user locked - dword: %x expected data: %x\n", ii, mbox_data[ii]);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }

    //// MBOX: Write DLEN
    VPRINTF(LOW, "MCU: Writing MBOX DLEN\n"); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN, 0xDEADBEEF);

    VPRINTF(LOW, "MCU: Reading MBOX DLEN\n"); 
    if (lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN) != 0xDEADBEEF) {
        VPRINTF(FATAL, "MCU: Wasn't able to write DLEN during user MB lock\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    //// MBOX: Write CMD
    VPRINTF(LOW, "MCU: Writing MBOX_CMD\n"); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD, 0xDEADBEEF);

    VPRINTF(LOW, "MCU: Reading MBOX DLEN\n"); 
    if (lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD) != 0xDEADBEEF) {
        VPRINTF(FATAL, "MCU: Wasn't able to write CMD during user MB lock\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    //// MBOX: Write CMD_STATUS
    VPRINTF(LOW, "MCU: Writing MBOX_CMD_STATUS\n"); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS, 0xDEADBEEF);

    if (lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS) != (0xDEADBEEF & MCU_MBOX0_CSR_MBOX_CMD_STATUS_STATUS_MASK)) {
        VPRINTF(FATAL, "MCU: Wasn't able to write CMD_STATUS during user MB lock\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    //// MBOX: Try writing MBOX_USER
    VPRINTF(LOW, "MCU: Trying MBOX_USER Write\n"); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER, 0xDEADBEEF);

    if (lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER) == 0xDEADBEEF) {
        VPRINTF(FATAL, "MCU: Was able to change read-only MBOX_USER register\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    //// MBOX: Try writing MBOX_LOCK
    VPRINTF(LOW, "MCU: Trying MBOX_LOCK write\n"); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK, 0x0);

    if (lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK) != 0x1) {
        VPRINTF(FATAL, "MCU: Was able to change read-only MBOX_LOCK register\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    //// MBOX: Try writing HW_STATUS
    VPRINTF(LOW, "MCU: Trying HW_STATUS write\n"); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_HW_STATUS, MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_SINGLE_ERROR_MASK | MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_DOUBLE_ERROR_MASK);
    
    if (lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_HW_STATUS) != 0x0) {
        VPRINTF(FATAL, "MCU: Was able to change read-only HW_STATUS register\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    //// MBOX: Write TARGET_USER
    VPRINTF(LOW, "MCU: Writing TARGET_USER write\n"); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER, 0xDEADBEEF);

    if (lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER) != 0xDEADBEEF) {
        VPRINTF(FATAL, "MCU: Wasn't able to write TARGET_USER during user MB lock\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    //// MBOX: Write TARGET_USER_VALID
    VPRINTF(LOW, "MCU: Writing TARGET_USER_VALID write\n"); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID, MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID_VALID_MASK);

    if (lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID) != MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID_VALID_MASK) {
        VPRINTF(FATAL, "MCU: Wasn't able to write TARGET_USER_VALID during user MB lock\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    //// MBOX: Clear execute
    VPRINTF(LOW, "MCU: Clearing Execute\n");
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE, 0x0);

    if (lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE) != 0) {
        VPRINTF(FATAL, "MCU: Wasn't able to write EXECUTE during user MB lock\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}

// Test (in conjuction with Caliptra uC C code) does a series of MCU mailbox writes and reads between MCU and Caliptra uC
// 1. Caliptra uC acquires mailbox, writes data to SRAM, sets EXECUTE
// 2. MCU waits for execute, writes SRAM and CSRs, reads them back to confirm write could occur
// 3. Caliptra uC will clear execute

void main (void) {
    int argc=0;
    char *argv[1];
    enum boot_fsm_state_e boot_fsm_ps;
    const uint32_t mbox_dlen = 16*4;
    uint32_t mbox_resp_dlen;
    uint32_t mbox_resp_data;
    uint32_t mci_boot_fsm_go;
    uint32_t sram_data;  
    uint32_t axi_select = xorshift32() % 5;

    uint32_t axi_user_id[] = { xorshift32(), xorshift32(), xorshift32(), xorshift32(), xorshift32() };
    VPRINTF(LOW, "MCU: Configured Valid AXI USERs: 0 - 0x%x; 1 - 0x%x; 2 - 0x%x; 3 - 0x%x; 4 - 0x%x;\n", axi_user_id[0], axi_user_id[1], axi_user_id[2], axi_user_id[3], axi_user_id[4]);
    
    uint32_t caliptra_uc_axi_id = axi_user_id[axi_select];
    VPRINTF(LOW, "MCU: Valid AXI USER for test AXI: 0x%x;\n", caliptra_uc_axi_id);

    VPRINTF(LOW, "=================\nMCU Configure MCI mailboxes\n=================\n\n")
    // MBOX: Setup valid AXI
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_0, axi_user_id[0]);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_1, axi_user_id[1]);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_2, axi_user_id[2]);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_3, axi_user_id[3]);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_4, axi_user_id[4]);

    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_0, MCI_REG_MBOX0_AXI_USER_LOCK_0_LOCK_MASK);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_1, MCI_REG_MBOX0_AXI_USER_LOCK_1_LOCK_MASK);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_2, MCI_REG_MBOX0_AXI_USER_LOCK_2_LOCK_MASK);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_3, MCI_REG_MBOX0_AXI_USER_LOCK_3_LOCK_MASK);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_4, MCI_REG_MBOX0_AXI_USER_LOCK_4_LOCK_MASK);

    mcu_mci_boot_go();

    VPRINTF(LOW, "MCU: Configured Caliptra as Valid AXI USER\n");
    lsu_write_32(SOC_SOC_IFC_REG_SS_CALIPTRA_DMA_AXI_USER, caliptra_uc_axi_id);

    VPRINTF(LOW, "MCU: Caliptra bringup\n")

    mcu_cptra_fuse_init();

    mcu_mbox_clear_lock_out_of_reset();

    ////////////////////////////////////
    // Mailbox command test
    ////////////////////////////////////

    // Wait for Caliptra Core to acquire lock, write MBOX data, and set execute
    // Do writes to SRAM and CSRs and verify that write occured with reads.
    mcu_mbox_wait_for_lock_and_execute();
    
    mcu_mbox0_write_sram_and_csrs();

    VPRINTF(LOW, "MCU: Sequence complete\n");

    SEND_STDOUT_CTRL(0xff);
}
