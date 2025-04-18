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

static const char* mcu_hitless_sram_msg __attribute__ ((section(".mcu_hitless_sram.msg"))) = "=========\nHello World from MCU SRAM Hitless Update\n==========\n";
static bool mcu_hitless_sram_flag __attribute__((section(".mcu_hitless_sram.flag"))) = true;
static uint32_t test_sram_data __attribute__ ((section(".mcu_hitless_sram.test_sram_data"))) = 0;
bool mcu_hitless_sram_print_msg (void) __attribute__ ((aligned(4),section (".mcu_hitless_sram.print_msg"),noinline));

bool mcu_hitless_sram_print_msg (void) {
    
    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_4)) {
        test_sram_data = lsu_read_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_4);
    }
    VPRINTF(LOW, "MCU: Test_sram_data: 0x%x;\n", test_sram_data);

    VPRINTF(LOW, mcu_hitless_sram_msg);
    
    return (mcu_hitless_sram_flag && (test_sram_data != 0));
}
// Test (in conjuction with Caliptra uC C code) exercises the hitless flow 
// 
// -SOC BFM will acquire mbox lock (standing in as proxy for soc agent)
// -SOC BFM load FW image in to mailbox (pre-compiled image)
// -MCU will set target user (to Caliptra uC) and target user valid; send caliptra mailbox cmd? to process
// -Caliptra uC reads and processes image (in this case, just read do a few reads for testing purpose
// -Caliptra set interrupt for notif_cptra_mcu_reset_req_sts 
// -Caliptra clears FW_EXEC_CTRL[2] indicating a FW image is ready for MCU.
// -MCU sees request from Caliptra clears the interrupt status.
// -MCU sets RESET_REQUEST.mcu_req in MCI to request a hitless reset 
// -Caliptra polls on RESET_STATUS.MCU_RESET to see that reset is complete
// -Caliptra will gain access to MCU SRAM Updatable Execution Region and update the FW image.
// -Caliptra sets RESET_REASON.FW_HITLESS_UPD_RESET
// -Caliptra sets FW_EXEC_CTRL[2]
// -MCU is brought out of reset and checks MCI's RESET_REASON
// -MCU jumps to MCU SRAM
// -MCU new firmware will print out hello world/look at boolean flag and stored in hitless image in SRAM and pass the test if it is FW_HITLESS_UPD_RESET

void main (void) {
    int argc=0;
    char *argv[1];

    // If hitless update is the reset reason then print out the message that is executing out of SRAM
    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_RESET_REASON) & MCI_REG_RESET_REASON_FW_HITLESS_UPD_RESET_MASK) {

        // MBOX: Poll status
        VPRINTF(LOW, "MCU: Waiting for Caliptra Mbox Status\n");
        if(!mcu_cptra_mbox_wait_for_status(10000, CMD_COMPLETE)) {
            VPRINTF(FATAL, "MCU: Mbox%x Caliptra Mbox status not set\n", decode_single_valid_mbox());
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        VPRINTF(LOW, "MCU: Caliptra Mbox responded with cmd_complete\n");

        // MBOX: Clear Execute in Caliptra
        lsu_write_32(SOC_MBOX_CSR_MBOX_EXECUTE, 0);
        VPRINTF(LOW, "MCU: Caliptra Mbox execute clear\n");

        // MBOX: Set complete in MCU Mbox
        mcu_mbox_write_cmd_status(decode_single_valid_mbox(), MCU_MBOX_CMD_COMPLETE);

        bool success = false;

        // MCU Hitless SRAM code to print message and check boolean runs out of udpated MCU SRAM
        if(mcu_hitless_sram_print_msg()) {
            SEND_STDOUT_CTRL(0xFF);
        } else {
            SEND_STDOUT_CTRL(0x1);
        }
        while(1);

    } else if (lsu_read_32(SOC_MCI_TOP_MCI_REG_RESET_REASON) & MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_MASK){
        // This section is to emulate an initial FW_BOOT_UPD_RESET scenario to exercise FW_CTRL[2] state tracking HW
        // This will still run out of ROM and handle rest of handshake for doing the hitless update as the MCU SRAM
        // is preloaded with random data to test out hitless update
        lsu_write_32(SOC_MCI_TOP_MCI_REG_RESET_REASON, 0);
        
        // Wait for Reset req sts interrupt
        if(!mcu_wait_for_mcu_reset_req_interrupt(10000)) {
            VPRINTF(FATAL, "MCU: Reset Request Interrupt not set\n", decode_single_valid_mbox());
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        
        // Clear Reset req sts interrupt
        mcu_clear_reset_req_interrupt();

        // Set RESET_REQUEST.mcu_req
        VPRINTF(LOW, "MCU: Issuing reset for Hitless Update\n\n");
        mcu_mci_req_reset();
        while(1);
    } else {

        enum boot_fsm_state_e boot_fsm_ps;
        uint32_t mbox_resp_dlen;
        uint32_t mbox_resp_data;
        uint32_t mci_boot_fsm_go;
        uint32_t sram_data;  
        uint32_t mbox_num = decode_single_valid_mbox();
        bool     mbox0_sel = true;

        uint32_t caliptra_uc_axi_id = lsu_read_32(SOC_MCI_TOP_MCI_REG_MCU_SRAM_CONFIG_AXI_USER);

        uint32_t axi_user_id[] = {0x12345678, caliptra_uc_axi_id, xorshift32(), xorshift32(), xorshift32() };

        VPRINTF(LOW, "MCU: Caliptra AXI for test: 0x%x;\n", caliptra_uc_axi_id);

        VPRINTF(LOW, "=================\nMCU Configure MCI mailboxes\n=================\n\n")
        
        if(mbox_num) {
            mbox0_sel = false;
        }

        mcu_cptra_init_d(.cfg_enable_cptra_mbox_user_init=true, .cfg_cptra_dma_axi_user=true, .cptra_dma_axi_user=caliptra_uc_axi_id, .cfg_mcu_mbox0_valid_user=mbox0_sel, .mcu_mbox0_valid_user=axi_user_id, .cfg_mcu_mbox1_valid_user=!mbox0_sel, .mcu_mbox1_valid_user=axi_user_id);

        mcu_mbox_clear_lock_out_of_reset(mbox_num);

        ////////////////////////////////////
        // Mailbox command test
        ////////////////////////////////////

        // Wait for SOC Data Available Interrupt (sample hitless FW image will be written from BFM sequence mcu_mbox_soc_agent_write_fw_image.svh)
        if(!mcu_mbox_wait_for_soc_data_avail_interrupt(mbox_num, 100000)) {
            VPRINTF(FATAL, "MCU: Mbox%x SOC Data Available Interrupt not set\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        mcu_mbox_clear_soc_req_while_mcu_lock_interrupt(mbox_num);

        if (mcu_mbox_read_cmd(mbox_num) != 0xABCD) {
            VPRINTF(FATAL, "MCU: Mbox%x CMD was not exepcted\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        // Set TARGET_USER and TARGET_USER_VALID
        mcu_mbox_write_target_user(mbox_num, caliptra_uc_axi_id);
        mcu_mbox_write_target_user_valid(mbox_num, 1);

        mcu_cptra_poll_mb_ready();

        // Send cmd to Caliptra MBOX
        // MBOX: Acquire lock
        VPRINTF(LOW, "MCU: Waiting for Caliptra Mbox lock\n");
        if(!mcu_cptra_mbox_acquire_lock(1000)) {
            VPRINTF(FATAL, "MCU: Mbox%x Caliptra did not acquire lock\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        VPRINTF(LOW, "MCU: Caliptra Mbox lock acquired\n");

        // MBOX: Write CMD
        lsu_write_32(SOC_MBOX_CSR_MBOX_CMD, 0x1234);

        // MBOX: Write DLEN
        lsu_write_32(SOC_MBOX_CSR_MBOX_DLEN, 0x1);

        // MBOX: Write DATIN
        lsu_write_32(SOC_MBOX_CSR_MBOX_DATAIN, 0x1);

        // MBOX: Execute
        lsu_write_32(SOC_MBOX_CSR_MBOX_EXECUTE, MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);
        VPRINTF(LOW, "MCU: Caliptra Mbox execute\n");

        // MBOX: Wait for Reset req sts interrupt
        if(!mcu_wait_for_mcu_reset_req_interrupt(10000)) {
            VPRINTF(FATAL, "MCU: Reset Request Interrupt not set\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        mcu_clear_reset_req_interrupt();

        // Set RESET_REQUEST.mcu_req
        VPRINTF(LOW, "MCU: Issuing reset for FW_BOOT_UPD_RESET\n\n");
        mcu_mci_req_reset();

        while(1);
    }
}
