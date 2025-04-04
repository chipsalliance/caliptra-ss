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

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void mcu_mbox0_get_data(){
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

    VPRINTF(LOW, "MCU: Waiting for caliptra to acquire the lock\n");
    while(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER) == 0);
    
    VPRINTF(LOW, "MCU: Waiting for caliptra to set execute\n");
    while(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE) == 0)

    mbox_dlen = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN);
    VPRINTF(LOW, "MCU: Caliptra data length: 0x%x\n", mbox_dlen);

    for (uint32_t ii = 0; ii < mbox_dlen/4; ii++) {
        mbox_resp_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii));
        VPRINTF(LOW, "MCU: Reading Caliptra data from MBOX: Data[%d] 0x%x\n", ii, mbox_resp_data);
        // Compare expected data from Caliptra uC
        if (mbox_resp_data != clptra_expected_data[ii]) {
            VPRINTF(FATAL, "MCU: Mbox0 SRAM data from Caliptra is not expected value - dword: %x\n", ii);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }

    // MBOX: Write CMD
    VPRINTF(LOW, "MCU: Writing to MBOX status 0x2\n"); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS, 0x2 );

}

void mcu_mbox0_clear_execute() {
    uint32_t mbox_resp_data;
    VPRINTF(LOW, "MCU: Clearing Execute\n");
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE, 0x0);
    
    mbox_resp_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER);
    VPRINTF(LOW, "MCU: MBOX0 USER = %x\n", mbox_resp_data);

}

void mcu_mbox0_send_data_no_wait_status() {
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
    VPRINTF(LOW, "MCU: Waiting for Mbox lock acquired\n");
    while((lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK) & MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK));
    VPRINTF(LOW, "MCU: Mbox lock acquired\n");
    
    mbox_resp_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK);
    VPRINTF(LOW, "MCU: MBOX0 Lock = %x\n", mbox_resp_data);
    

    VPRINTF(LOW, "MCU: Checking MBOX USER\n");
    while(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER) == 0);
    mbox_resp_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER);
    VPRINTF(LOW, "MCU: MBOX0 USER = %x\n", mbox_resp_data);

    // MBOX: Write CMD
    VPRINTF(LOW, "MCU: Writing to MBOX command\n"); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD, 0xFADECAFE ); // Resp required

    //// MBOX: Write DLEN
    VPRINTF(LOW, "MCU: Writing to MBOX DLEN\n"); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN, mbox_dlen);

    //// MBOX: Write data
    for (uint32_t ii = 0; ii < mbox_dlen/4; ii++) {
        VPRINTF(LOW, "MCU: Writing to MBOX data: 0x%x\n", mbox_data[ii]); 
        lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii), mbox_data[ii]);
    }

    //// MBOX: Execute
    VPRINTF(LOW, "MCU: Write Mbox execute\n");
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE, MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);
    VPRINTF(LOW, "MCU: Mbox execute\n");
}

void mcu_mbox0_wait_status_complete() {
    VPRINTF(LOW, "MCU: Waiting status from Caliptra\n");
    while((lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS) & MBOX_CSR_MBOX_STATUS_STATUS_MASK) != 0x2);
}

// Test (in conjuction with Caliptra uC C code) does a series of MCU mailbox writes and reads between MCU and Caliptra uC
// 1. Caliptra uC acquires mailbox, writes data to SRAM, sets EXECUTE
// 2. MCU waits for execute, reads SRAM and compares to expected value, update MBOX status to complete
// 3. Caliptra uC will clear execute and wait for MCU.
// 4. MCU will acquire lock and write data to MCU MBOX and set execute
// 5. Caliptra will read data from the MCU MBOX SRAM and then set complete status
// 6. MCU will wait for status complete and then clear execute
void main (void) {
    int argc=0;
    char *argv[1];
    enum boot_fsm_state_e boot_fsm_ps;
    const uint32_t mbox_dlen = 16*4;
    uint32_t mbox_num = 0;
    uint32_t mbox_resp_dlen;
    uint32_t mbox_resp_data;
    uint32_t mci_boot_fsm_go;
    uint32_t sram_data;
    
    
    VPRINTF(LOW, "=================\nMCU Configure MCI mailboxes\n=================\n\n");

    VPRINTF(LOW, "MCU: Configured MBOX Valid AXI USER\n");

    mcu_mci_boot_go();

    VPRINTF(LOW, "MCU: Caliptra bringup\n");


    // Setting Caliptra to DEFAULT user
    mcu_cptra_fuse_init_axi_user(0xFFFFFFFF);


    mcu_mbox_clear_lock_out_of_reset(mbox_num);

    ////////////////////////////////////
    // Mailbox command test
    ////////////////////////////////////

    // Wait for Caliptra Core to acquire lock, write MBOX data, and set execute
    // Read MBOX data.  Check that data matches test expectation
    // Update status
    mcu_mbox0_get_data();

    // Acquire lock and send data to mailbox
    // Set execute
    mcu_mbox0_send_data_no_wait_status();

    mcu_mbox0_clear_execute();

    VPRINTF(LOW, "MCU: Sequence complete\n");

    SEND_STDOUT_CTRL(0xff);
}
