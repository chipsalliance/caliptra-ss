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


void mcu_mbox_get_and_check_sram_data(uint32_t mbox_num, uint32_t expected_dlen, uint32_t *clptra_expected_data) {

    uint32_t mbox_resp_data;

    uint32_t mbox_dlen = mcu_mbox_read_dlen(mbox_num);
    if (expected_dlen != mbox_dlen) {
        VPRINTF(FATAL, "MCU: Mbox%x Caliptra data length is not expected value - dword: %x\n", mbox_num, expected_dlen);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    for (uint32_t ii = 0; ii < mbox_dlen/4; ii++) {
        mbox_resp_data = mcu_mbox_read_sram(mbox_num, 4*ii);
        // Compare expected data from Caliptra uC
        if (mbox_resp_data != clptra_expected_data[ii]) {
            VPRINTF(FATAL, "MCU: Mbox%x SRAM data from Caliptra is not expected value - dword: %x expected data: %x\n", mbox_num, ii, clptra_expected_data[ii]);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }

}

void mcu_mbox_check_target_non_accessible_regs(uint32_t mbox_num, uint32_t caliptra_uc_axi_id, bool target_valid) {
    if(mcu_mbox_read_cmd(mbox_num) != 0xFADECAFE) {
        VPRINTF(FATAL, "MCU: Mbox%x CMD was changed by Target User\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if(mcu_mbox_read_cmd_status(mbox_num) != MCU_MBOX_DATA_READY) {
        VPRINTF(FATAL, "MCU: Mbox%x CMD_STATUS was changed by Target User\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    // TODO: add root user strap
    if (mcu_mbox_read_mbox_user(mbox_num) != 0x1) {
        VPRINTF(FATAL, "MCU: Mbox%x MBOX_USER was changed by Target User\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if (mcu_mbox_read_lock(mbox_num) != 1) {
        VPRINTF(FATAL, "MCU: Mbox%x MBOX Lock was changed by Target User\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if (mcu_mbox_read_hw_status(mbox_num) != 0) {
        VPRINTF(FATAL, "MCU: Mbox%x MBOX HW_STATUS was changed by Target User\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if (mcu_mbox_read_target_user(mbox_num) != caliptra_uc_axi_id) {
        VPRINTF(FATAL, "MCU: Mbox%x TARGET_USER was changed by Target User\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if (mcu_mbox_read_target_user_valid(mbox_num) != (uint32_t) target_valid ) {
        VPRINTF(FATAL, "MCU: Mbox%x TARGET_USER_VALID was changed by Target User\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}


void mcu_mbox_send_data_no_wait_status(uint32_t mbox_num, uint32_t mbox_dlen, uint32_t *mbox_data) {
    uint32_t mbox_resp_data;

    uint32_t mbox_resp_dlen;

    // MBOX: Write CMD
    mcu_mbox_write_cmd(mbox_num, 0xFADECAFE);

    //// MBOX: Write DLEN
    mcu_mbox_write_dlen(mbox_num, mbox_dlen);

    //// MBOX: Write SRAM data
    for (uint32_t ii = 0; ii < mbox_dlen/4; ii++) {
        mcu_mbox_write_sram(mbox_num, 4*ii, mbox_data[ii]);
    }

    // MBOX: Write CMD_STATUS for testing
    mcu_mbox_write_cmd_status(mbox_num, MCU_MBOX_DATA_READY);
}

// Test (in conjuction with Caliptra uC C code) exercise the TARGET_USER aspects of the MCU Mbox 
// Caliptra uC will be the target user
// 1. MCU acquires Mbox lock and writes information in the mailbox CSRs and SRAM and sets execute (without setting target user)
// 2. MCU will set TARGET_USER but not TARGET_USER_VALID and set execute
// 3. Caliptra uC will wait for execute and attempt writing/reading SRAM and reading/writing CSRs (all writing should fail and SRAM should return 0s)
// 4. Caliptra uC will attempt acquiring lock (as a sync point so MCU can see if any contents were able to be changed).
// 4. MCU will set TARGET_USER_VALID
// 5. Caliptra uC will read the mailbox CSRs and SRAM and check that the data is what was written by the MCU
// 6. Caliptra uC will attempt to write to the mailbox CSRs and SRAM and set TARGET_STATUS/DONE
// 7. MCU will check that only SRAM and DLEN has changed 

void main (void) {
    int argc=0;
    char *argv[1];
    enum boot_fsm_state_e boot_fsm_ps;
    uint32_t mbox_resp_dlen;
    uint32_t mbox_resp_data;
    uint32_t mci_boot_fsm_go;
    uint32_t sram_data;  
    uint32_t mbox_num = decode_single_valid_mbox();
    bool     mbox0_sel = true;

    uint32_t axi_user_id[] = { xorshift32(), xorshift32(), xorshift32(), xorshift32(), xorshift32() };
    uint32_t axi_select = xorshift32() % (sizeof(axi_user_id)/ sizeof(axi_user_id[0]));

    uint32_t caliptra_uc_axi_id = axi_user_id[axi_select];
    VPRINTF(LOW, "MCU: Caliptra Target User AXI for test: 0x%x;\n", caliptra_uc_axi_id);

    VPRINTF(LOW, "=================\nMCU Configure MCI mailboxes\n=================\n\n")
    
    if(mbox_num) {
        mbox0_sel = false;
    }

    mcu_cptra_init_d(.cfg_cptra_dma_axi_user=true, .cptra_dma_axi_user=caliptra_uc_axi_id, .cfg_mcu_mbox0_valid_user=mbox0_sel, .mcu_mbox0_valid_user=axi_user_id, .cfg_mcu_mbox1_valid_user=!mbox0_sel, .mcu_mbox1_valid_user=axi_user_id);

    mcu_mbox_clear_lock_out_of_reset(mbox_num);

    ////////////////////////////////////
    // Mailbox command test
    ////////////////////////////////////

    // MBOX: MCU Acquire lock
    if (!mcu_mbox_acquire_lock(mbox_num, 1000)) {
        VPRINTF(FATAL, "MCU: Mbox%x didn't acquire lock\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);        
    }

    // MBOX: MCU Wait for User to Reflect
    if(!mcu_mbox_wait_for_user_to_be_mcu(mbox_num, 1000)) {
        VPRINTF(FATAL, "MCU: Mbox%x didn't update mbox user appropriately\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);  
    }

    // Send data to mailbox
    uint32_t mcu_mbox_dlen = 64;
    uint32_t mcu_mbox_data[] = { 0x00000000,
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

    mcu_mbox_send_data_no_wait_status(mbox_num, mcu_mbox_dlen, mcu_mbox_data);

    // Set TARGET_USER
    mcu_mbox_write_target_user(mbox_num, caliptra_uc_axi_id);

    mcu_mbox_set_execute(mbox_num);

    // Wait for SOC request while MCU has lock interrupt
    // Caliptra uC will acquire lock after attempting writes and reads
    if (!mcu_mbox_wait_for_soc_req_while_mcu_lock_interrupt(mbox_num, 100000)) {
        VPRINTF(FATAL, "MCU: Mbox%x SoC req while MCU lock interrupt not set\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    mcu_mbox_clear_soc_req_while_mcu_lock_interrupt(mbox_num);

    // Check that TARGET was unable to change Mbox SRAM or CSRs
    mcu_mbox_get_and_check_sram_data(mbox_num, mcu_mbox_dlen, mcu_mbox_data);

    bool target_valid = false;
    mcu_mbox_check_target_non_accessible_regs(mbox_num, caliptra_uc_axi_id, target_valid);

    // Set TARGET_USER_VALID
    mcu_mbox_write_target_user_valid(mbox_num, 1);

    // Wait for TARGET_STATUS DONE and COMPLETE
    if (!mcu_mbox_wait_for_target_status_done(mbox_num, MCU_MBOX_TARGET_STATUS_COMPLETE, 10000)) {
        VPRINTF(FATAL, "MCU: Mbox%x Target status not done and complete\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Check that target done interrupt is set
    // Clear the target done interrupt
    if(!is_mcu_mbox_target_done_interrupt_set(mbox_num)) {
        VPRINTF(FATAL, "MCU: Mbox%x Target done interrupt not set\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    mcu_mbox_clear_target_done_interrupt(mbox_num);

    // Check that only SRAM, DLEN have changed
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

    uint32_t mbox_dlen = sizeof(clptra_expected_data);

    mcu_mbox_get_and_check_sram_data(mbox_num, mbox_dlen, clptra_expected_data);

    target_valid = true;
    mcu_mbox_check_target_non_accessible_regs(mbox_num, caliptra_uc_axi_id, target_valid);

    VPRINTF(LOW, "MCU: Sequence complete\n");

    SEND_STDOUT_CTRL(0xff);

    while(1);
}
