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
                                        0x12345678,
                                        0x86754321};

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

// Test (in conjuction with Caliptra uC C code) will test SoC sending data, MCU receiving, updating data back using data_ready status
// 1. Caliptra uC acquires mailbox, writes data to SRAM, sets EXECUTE
// 2. MCU waits for execute, reads SRAM and compares to expected value
// 3. MCU Checks SRAM data, writes back new SRAM data, sets status as data_ready
// 3. Caliptra uC will wait for status as data_ready.
// 4. Caliptra uC will read SRAM and check data and clear execute

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
    
    uint32_t caliptra_uc_axi_id = axi_user_id[axi_select];
    VPRINTF(LOW, "MCU: Valid AXI USER for test AXI: 0x%x;\n", caliptra_uc_axi_id);

    VPRINTF(LOW, "=================\nMCU Configure MCI mailboxes\n=================\n\n");

    if(mbox_num) {
        mbox0_sel = false;
    }

    mcu_cptra_init_d(.cfg_cptra_dma_axi_user=true, .cptra_dma_axi_user=caliptra_uc_axi_id, .cfg_mcu_mbox0_valid_user=mbox0_sel, .mcu_mbox0_valid_user=axi_user_id, .cfg_mcu_mbox1_valid_user=!mbox0_sel, .mcu_mbox1_valid_user=axi_user_id);

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

    // Send data to mailbox
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

    //// MBOX: Write SRAM data as DATA_READY response back to SOC
    for (uint32_t ii = 0; ii < mbox_dlen/4; ii++) {
        mcu_mbox_write_sram_dword(mbox_num, ii, mbox_data[ii]);
    }

    mcu_mbox_write_dlen(mbox_num, sizeof(mbox_data));

    mcu_mbox_update_status(mbox_num, MCU_MBOX_DATA_READY);

    VPRINTF(LOW, "MCU: Sequence complete\n");
    
    while(1);
}
