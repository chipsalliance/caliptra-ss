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
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


void mcu_mbox_get_data(uint32_t mbox_num){
    uint32_t clptra_expected_data[] = { 0x10101010,
                                        0x20202020,
                                        0x30303030,
                                        0x40404040,
                                        0x50505050,
                                        0x60606060,
                                        0x70707070,
                                        0x80808080,
                                        0x90909090,
                                        0xA0A0A0A0,
                                        0xB0B0B0B0,
                                        0xC0C0C0C0,
                                        0xD0D0D0D0,
                                        0xE0E0E0E0,
                                        0xF0F0F0F0,
                                        0x12345678 };

    uint32_t mbox_resp_data;
    uint32_t mbox_dlen;

    mbox_dlen = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "MCU: Mbox%x Caliptra data length: 0x%x\n", mbox_num, mbox_dlen);

    for (uint32_t ii = 0; ii < mbox_dlen/4; ii++) {
        mbox_resp_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii) + MCU_MBOX_NUM_STRIDE * mbox_num);
        VPRINTF(LOW, "MCU: Reading Caliptra data from MBOX%x: Data[%d] 0x%x\n", mbox_num, ii, mbox_resp_data);
        // Compare expected data from Caliptra uC
        if (mbox_resp_data != clptra_expected_data[ii]) {
            VPRINTF(FATAL, "MCU: Mbox%x SRAM data from Caliptra is not expected value - dword: %x expected data: %x\n", mbox_num, ii, clptra_expected_data[ii]);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }

}

void mcu_mbox_send_data_no_wait_status(uint32_t mbox_num) {
    uint32_t mbox_resp_data;
    const uint32_t mbox_dlen = 16*4;
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
    uint32_t mbox_resp_dlen;

    // MBOX: Acquire lock
    if (!mcu_mbox_acquire_lock(mbox_num, 1000)) {
        VPRINTF(FATAL, "MCU: Mbox%x didn't acquire lock\n", mbox_num);
    }
    
    mbox_resp_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "MCU: MBOX%x Lock = %x\n", mbox_num, mbox_resp_data);
    
    VPRINTF(LOW, "MCU: Wait for Lock to Reflect MBOX USER\n");
    if(!mcu_mbox_wait_for_user_to_be_mcu(mbox_num, 1000)) {
        VPRINTF(FATAL, "MCU: Mbox%x didn't update mbox user appropriately\n", mbox_num);
    }

    // MBOX: Write CMD
    VPRINTF(LOW, "MCU: Writing to MBOX%x command\n", mbox_num); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + MCU_MBOX_NUM_STRIDE * mbox_num, 0xFADECAFE );

    //// MBOX: Write DLEN
    VPRINTF(LOW, "MCU: Writing to MBOX%x DLEN\n", mbox_num); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num, mbox_dlen);

    //// MBOX: Write data
    for (uint32_t ii = 0; ii < mbox_dlen/4; ii++) {
        VPRINTF(LOW, "MCU: Writing to MBOX%x data: 0x%x\n", mbox_num, mbox_data[ii]); 
        lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii) + MCU_MBOX_NUM_STRIDE * mbox_num, mbox_data[ii]);
    }

    // MBOX: Write CMD_STATUS for testing
    VPRINTF(LOW, "MCU: Writing to MBOX%x CMD_STATUS\n", mbox_num); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, 0x1 );    

    //// MBOX: Execute
    VPRINTF(LOW, "MCU: Write Mbox execute\n");
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);
    VPRINTF(LOW, "MCU: Mbox%x execute\n", mbox_num);
}

// Test (in conjuction with Caliptra uC C code) does a series of MCU mailbox writes and reads between MCU and Caliptra uC
// 1. Caliptra uC acquires mailbox, writes data to SRAM, sets EXECUTE
// 2. MCU waits for execute, reads SRAM and compares to expected value, checks MBOX_USER matches Caliptra uC
// 3. Caliptra uC will clear execute and wait for MCU.
// 4. MCU will acquire lock and write data to MCU MBOX and set execute
// 5. Caliptra will read data from the CSRs, MCU MBOX SRAM (expecting all 0's), and attempt writes and reads to SRAM and CSRs
// 6. MCU mark status complete and then wait for test to finish

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
    uint32_t axi_select = xorshift32() % 5;

    uint32_t axi_user_id[] = { xorshift32(), xorshift32(), xorshift32(), xorshift32(), xorshift32() };
    
    uint32_t caliptra_uc_axi_id = axi_user_id[axi_select];
    VPRINTF(LOW, "MCU: Valid AXI USER for test AXI: 0x%x;\n", caliptra_uc_axi_id);

    VPRINTF(LOW, "=================\nMCU Configure MCI mailboxes\n=================\n\n")
    // MBOX: Setup valid AXI
    mcu_mbox_configure_valid_axi(mbox_num, axi_user_id);

    mcu_mci_boot_go();

    VPRINTF(LOW, "MCU: Configured Caliptra as Valid AXI USER\n");
    lsu_write_32(SOC_SOC_IFC_REG_SS_CALIPTRA_DMA_AXI_USER, caliptra_uc_axi_id);

    VPRINTF(LOW, "MCU: Caliptra bringup\n")

    mcu_cptra_fuse_init();

    mcu_mbox_clear_lock_out_of_reset(mbox_num);

    ////////////////////////////////////
    // Mailbox command test
    ////////////////////////////////////

    // Wait for Caliptra Core to acquire lock, write MBOX data, and set execute
    // Read MBOX data.  Check that data matches test expectation
    // Update status
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

    mcu_mbox_get_data(mbox_num);

    // Check that User CSR properly displays lock user
    if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num) != caliptra_uc_axi_id) {
        VPRINTF(FATAL, "MCU: Mbox%x Caliptra AXI not reflected in MBOX_USER CSR\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    VPRINTF(LOW, "MCU: Mbox%x Caliptra AXI properly reflected in MBOX_USER CSR\n", mbox_num);

    mcu_mbox_update_status_complete(mbox_num);

    // Clear the interrupt and check that it gets cleared
    mcu_mbox_clear_mbox_cmd_avail_interrupt(mbox_num);

    // Acquire lock and send data to mailbox
    // Set execute
    mcu_mbox_send_data_no_wait_status(mbox_num);

    VPRINTF(LOW, "MCU: Sequence complete\n");

    while(1);
}
