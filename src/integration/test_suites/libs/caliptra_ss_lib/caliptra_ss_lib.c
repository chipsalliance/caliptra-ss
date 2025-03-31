// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
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
//

#include "soc_address_map.h"
#include "printf.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "riscv_hw_if.h"
#include "string.h"
#include "stdint.h"
#include "caliptra_ss_clk_freq.h"
#include "caliptra_ss_lib.h"
#include <stdbool.h>


#ifdef MY_RANDOM_SEED
    uint32_t state = (unsigned) MY_RANDOM_SEED;
#else
    uint32_t state = 0;
#endif

uint32_t xorshift32(void)
{
    state ^= state << 13;
    state ^= state >> 17;
    state ^= state << 5;
    return state;
}

inline void mcu_sleep (const uint32_t cycles) {
    for (uint8_t ii = 0; ii < cycles; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
}

void reset_fc_lcc_rtl(void) {
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FC_LCC_RESET);
    VPRINTF(LOW, "LCC & Fuse_CTRL is under reset!\n");
    mcu_sleep(160);
}

void read_check(uintptr_t rdptr, uint32_t expected_rddata){
    uint32_t data;
    data = lsu_read_32(rdptr);
    VPRINTF(LOW, "read_check: Address: 0x%x -- Expected: 0x%x Actual: 0x%x\n", rdptr, expected_rddata, data);
    if (expected_rddata != data) {
        VPRINTF(FATAL, "MCU: FATAL - read_check: Data mismatch at address: 0x%x -- Expected: 0x%x Actual: 0x%x\n", rdptr, expected_rddata, data);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}


void mcu_mci_boot_go() {
 
    // Configure EXEC Region before initializing Caliptra
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_SRAM_EXEC_REGION_SIZE , 100);
    VPRINTF(LOW, "MCU: Configure EXEC REGION Size\n");
    

    // writing SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO register of MCI for CPTRA Boot FSM to bring Caliptra out of reset
    uint32_t cptra_boot_go;
    VPRINTF(LOW, "MCU: Writing MCI SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, 1);
    
    VPRINTF(LOW, "MCU: Reading SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO");
    cptra_boot_go = lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO);
    VPRINTF(LOW, "MCU: SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO set to %x\n", cptra_boot_go);
}

void mcu_mci_poll_exec_lock() {
    uint32_t rg;
    uint32_t cnt = 0;
    do {
        mcu_sleep(64);
        if (!(cnt++ & 0xf)) {
            VPRINTF(MEDIUM, " * poll ex lk %x\n", cnt);
        }
        rg = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MCU_RESET_REQ_STS_MASK;
    } while(rg != MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MCU_RESET_REQ_STS_MASK);
}

void mcu_mci_req_reset() {
    lsu_write_32(SOC_MCI_TOP_MCI_REG_RESET_REQUEST, MCI_REG_RESET_REQUEST_MCU_REQ_MASK);
}

void mcu_cptra_wait_for_fuses() {
    // Wait for ready_for_fuses
    VPRINTF(LOW, "MCU: Wait for CPTRA FLOW STATUS\n");
    while(!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK));
    VPRINTF(LOW, "MCU: CPTRA FLOW STATUS COMPLETE\n");

}

void mcu_cptra_set_fuse_done() {
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_FUSE_WR_DONE, SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
    VPRINTF(LOW, "MCU: Set fuse wr done\n");
}

void mcu_cptra_advance_brkpoint() {
    enum boot_fsm_state_e boot_fsm_ps;
    
    VPRINTF(LOW, "MCU: Waiting for CPTRA BOOT_DONE or BOOT_WAIT\n");
    // Wait for Boot FSM to stall (on breakpoint) or finish bootup
    boot_fsm_ps = (lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK) >> SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW;
    while(boot_fsm_ps != BOOT_DONE && boot_fsm_ps != BOOT_WAIT) {
        mcu_sleep(16);
        boot_fsm_ps = (lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK) >> SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW;
    }

    // Advance from breakpoint, if set
    if (boot_fsm_ps == BOOT_WAIT) {
        VPRINTF(LOW, "MCU: CPTRA BOOT_WAIT setting BootFSM GO\n");
        lsu_write_32(SOC_SOC_IFC_REG_CPTRA_BOOTFSM_GO, SOC_IFC_REG_CPTRA_BOOTFSM_GO_GO_MASK);
    }

    VPRINTF(LOW, "MCU: CPTRA FSM in BOOT_DONE\n");

}

void mcu_cptra_fuse_init_axi_user(uint32_t cptra_axi_user){
    ////////////////////////////////////
    // Fuse and Boot Bringup
    //
    mcu_cptra_wait_for_fuses();

    lsu_write_32(SOC_SOC_IFC_REG_SS_CALIPTRA_DMA_AXI_USER, cptra_axi_user);

    // Initialize fuses
    // TODO set actual fuse values
    mcu_cptra_set_fuse_done();

    mcu_cptra_advance_brkpoint();
}

void mcu_cptra_fuse_init() {
    enum boot_fsm_state_e boot_fsm_ps;

    ////////////////////////////////////
    // Fuse and Boot Bringup
    //
    mcu_cptra_wait_for_fuses();


    // Initialize fuses
    // TODO set actual fuse values
    mcu_cptra_set_fuse_done();

    mcu_cptra_advance_brkpoint();

}

void mcu_cptra_user_init() {
    // MBOX: Setup valid AXI USER
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0, 0x1); // FIXME this should come from a param for LSU AxUSER
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_1, 1);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_2, 2);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_3, 3);
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_MASK);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1_LOCK_MASK);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2_LOCK_MASK);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3_LOCK_MASK);
    VPRINTF(LOW, "MCU: Configured MBOX Valid AXI USER\n");

}

void mcu_mbox_clear_lock_out_of_reset(uint32_t mbox_num) {
    // MBOX: Write DLEN  (normally would be max SRAM size but using smaller size for test run time)
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE*mbox_num, 32);

    // MBOX: Clear Execute
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE*mbox_num, 0);
    VPRINTF(LOW, "MCU: Mbox%x execute clear\n", mbox_num);
    
    VPRINTF(LOW, "MCU: Mbox%x Lock out of reset cleared\n", mbox_num);
}

void mcu_mbox_update_status_complete(uint32_t mbox_num) {
    // MBOX: Write CMD
    VPRINTF(LOW, "MCU: Writing to MBOX status 0x2\n"); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE*mbox_num, 0x2 );
}

bool mcu_mbox_wait_for_user_lock(uint32_t mbox_num, uint32_t user_axi, uint32_t attempt_count) {
    VPRINTF(LOW, "MCU: Waiting for caliptra to acquire the lock in mbox%x\n", mbox_num);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num) == user_axi){
            VPRINTF(LOW, "MCU: Caliptra acquired Mbox%x lock\n", mbox_num);
            return true;
        }
    } 
    return false;
}

bool mcu_mbox_wait_for_user_execute(uint32_t mbox_num, uint32_t attempt_count) {
    VPRINTF(LOW, "MCU: Waiting for caliptra to set execute in mbox%x\n", mbox_num);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num)){
            VPRINTF(LOW, "MCU: Caliptra set execute for Mbox%x\n", mbox_num);

            // Check that Mailbox cmd available from SOC interrupt has been set
            if((lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & 
                (MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_CMD_AVAIL_STS_MASK << mbox_num)) == 0) {
                VPRINTF(FATAL, "MCU: Mbox%x Mailbox cmd available from SoC interrupt not set\n", mbox_num);
                SEND_STDOUT_CTRL(0x1);
                while(1);
                }
            return true;
        }
    }
    return false;
}

void mcu_mbox_clear_mbox_cmd_avail_interrupt(uint32_t mbox_num) {
    VPRINTF(LOW, "MCU: RW1C cmd available interrupt Mbox%x\n", mbox_num);
    uint32_t internal_intr = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R);
    internal_intr |= MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_CMD_AVAIL_STS_MASK << mbox_num;
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R, internal_intr);

    // Check that Mailbox cmd available from SOC interrupt has been cleared
    if((lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & 
        (MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_CMD_AVAIL_STS_MASK << mbox_num)) == 1) {
        VPRINTF(FATAL, "MCU: Mbox%x Mailbox cmd available from SoC interrupt not set\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}

void mcu_mbox_configure_valid_axi(uint32_t mbox_num, uint32_t *axi_user_id) {
    
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_0 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, axi_user_id[0]);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_1 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, axi_user_id[1]);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_2 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, axi_user_id[2]);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_3 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, axi_user_id[3]);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_4 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, axi_user_id[4]);

    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_0 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, MCI_REG_MBOX0_AXI_USER_LOCK_0_LOCK_MASK);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_1 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, MCI_REG_MBOX0_AXI_USER_LOCK_1_LOCK_MASK);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_2 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, MCI_REG_MBOX0_AXI_USER_LOCK_2_LOCK_MASK);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_3 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, MCI_REG_MBOX0_AXI_USER_LOCK_3_LOCK_MASK);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_4 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, MCI_REG_MBOX0_AXI_USER_LOCK_4_LOCK_MASK);

    VPRINTF(LOW, "MCU: Configured Valid AXI USERs in Mbox%x:  0 - 0x%x; 1 - 0x%x; 2 - 0x%x; 3 - 0x%x; 4 - 0x%x;\n", mbox_num, axi_user_id[0], axi_user_id[1], axi_user_id[2], axi_user_id[3], axi_user_id[4]);
}

bool mcu_mbox_acquire_lock(uint32_t mbox_num, uint32_t attempt_count) {
    VPRINTF(LOW, "MCU: Waiting for Mbox%x lock acquired\n", mbox_num);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        if(!(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK + MCU_MBOX_NUM_STRIDE * mbox_num) & MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK)){
            VPRINTF(LOW, "MCU: Mbox%x lock acquired\n", mbox_num);
            return true;
        }
    }
    return false;
}

bool mcu_mbox_wait_for_user_to_be_mcu(uint32_t mbox_num, uint32_t attempt_count) {
    // TODO: update with MCU Root Strap Value
    uint32_t mbox_resp_data;
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        mbox_resp_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num);
        if(mbox_resp_data != 0){
            VPRINTF(LOW, "MCU: MBOX%x USER = %x\n", mbox_num, mbox_resp_data);
            return true;
        }
    }
    return false;
}

void mcu_cptra_poll_mb_ready() {
    // MBOX: Wait for ready_for_mb_processing
    while(!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK)) {
        mcu_sleep(16);
    }
    VPRINTF(LOW, "MCU: Ready for FW\n");
}

void mcu_cptra_mbox_cmd() {
    const uint32_t mbox_dlen = 64;
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
    uint32_t mbox_resp_data;

    // MBOX: Acquire lock
    while((lsu_read_32(SOC_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK));
    VPRINTF(LOW, "MCU: Mbox lock acquired\n");

    // MBOX: Write CMD
    lsu_write_32(SOC_MBOX_CSR_MBOX_CMD, 0xFADECAFE | MBOX_CMD_FIELD_RESP_MASK); // Resp required

    // MBOX: Write DLEN
    lsu_write_32(SOC_MBOX_CSR_MBOX_DLEN, 64);

    // MBOX: Write datain
    for (uint32_t ii = 0; ii < mbox_dlen/4; ii++) {
        lsu_write_32(SOC_MBOX_CSR_MBOX_DATAIN, mbox_data[ii]);
    }

    // MBOX: Execute
    lsu_write_32(SOC_MBOX_CSR_MBOX_EXECUTE, MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);
    VPRINTF(LOW, "MCU: Mbox execute\n");

    // MBOX: Poll status
    while(((lsu_read_32(SOC_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_STATUS_MASK) >> MBOX_CSR_MBOX_STATUS_STATUS_LOW) != DATA_READY) {
        mcu_sleep(16);
    }
    VPRINTF(LOW, "MCU: Mbox response ready\n");

    // MBOX: Read response data length
    mbox_resp_dlen = lsu_read_32(SOC_MBOX_CSR_MBOX_DLEN);

    // MBOX: Read dataout
    for (uint32_t ii = 0; ii < (mbox_resp_dlen/4 + (mbox_resp_dlen%4 ? 1 : 0)); ii++) {
        mbox_resp_data = lsu_read_32(SOC_MBOX_CSR_MBOX_DATAOUT);
    }
    VPRINTF(LOW, "MCU: Mbox response received\n");

    // MBOX: Clear Execute
    lsu_write_32(SOC_MBOX_CSR_MBOX_EXECUTE, 0);
    VPRINTF(LOW, "MCU: Mbox execute clear\n");
}

// -- function to update various register to default values
// PROT_CAP, DEVICE_ID, HW_STATUS, DEVICE_STATUS
void boot_i3c_reg(void) {

    uint32_t i3c_reg_data;
    //-- PROT_CAP
    VPRINTF(LOW, "MCU: Updating I3C Recovery Registers..\n");
    
    i3c_reg_data = 0x2050434f;
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_0, i3c_reg_data);
    VPRINTF(LOW, "MCU: Wr PROT_CAP_0 with 'h %0x\n", i3c_reg_data);
    i3c_reg_data = 0x56434552;
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_1, i3c_reg_data);
    VPRINTF(LOW, "MCU: Wr PROT_CAP_1 with 'h %0x\n", i3c_reg_data);    

    //-- DEVICE_ID
    i3c_reg_data = 0x00000001; //-- Dummy value
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_0, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_1, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_2, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_3, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_4, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_5, i3c_reg_data++);
    VPRINTF(LOW, "MCU: Wr DEVICE_ID with 'h %0x\n", i3c_reg_data);

    //-- HW_STATUS
    i3c_reg_data = 0x00000100; //-- Dummy value
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS, i3c_reg_data);
    VPRINTF(LOW, "MCU: Wr HW_STATUS with 'h %0x\n", i3c_reg_data);

    //-- DEVICE_STATUS
    i3c_reg_data = 0x00000001; //-- DEVICE_HEALTHY
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0, i3c_reg_data);

}

// -- function boot standby ctrl mode
// tb.reg_map.I3C_EC.STDBYCTRLMODE.STBY_CR_CONTROL.STBY_CR_ENABLE_INIT = 2
// tb.reg_map.I3C_EC.STDBYCTRLMODE.STBY_CR_CONTROL.TARGET_XACT_ENABLE = 1
void boot_i3c_standby_ctrl_mode(){
    uint32_t i3c_reg_data;
    i3c_reg_data = 0x00000000;

    VPRINTF(LOW, "MCU: boot_i3c_standby_ctrl_mode register writes \n");
    i3c_reg_data = lsu_read_32( SOC_I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL);
    i3c_reg_data = 2 << I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_STBY_CR_ENABLE_INIT_LOW | i3c_reg_data;
    i3c_reg_data = 1 << I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_TARGET_XACT_ENABLE_LOW | i3c_reg_data;
    lsu_write_32( SOC_I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL, i3c_reg_data);

}

// Helper function to write I3C SOCMGMTIF registers
void write_i3c_socmgmtif_registers(uint32_t t_r, uint32_t t_f, uint32_t t_hd_dat, uint32_t t_su_dat) {
    VPRINTF(LOW, "MCU: boot_i3c_socmgmt_if register writes \n");
    lsu_write_32(SOC_I3CCSR_I3C_EC_SOCMGMTIF_T_R_REG, t_r);
    lsu_write_32(SOC_I3CCSR_I3C_EC_SOCMGMTIF_T_F_REG, t_f);
    lsu_write_32(SOC_I3CCSR_I3C_EC_SOCMGMTIF_T_HD_DAT_REG, t_hd_dat);
    lsu_write_32(SOC_I3CCSR_I3C_EC_SOCMGMTIF_T_SU_DAT_REG, t_su_dat);
}

//-- function to boot i3c socmgmt interface
void boot_i3c_socmgmt_if(void) {
    uint32_t i3c_reg_data;

    // Read clock frequency from configuration file
    // file name : caliptra_ss_clk_freq.h
    uint32_t clk_freq = CALIPTRA_SS_CLK_FREQ;
    VPRINTF(LOW, "MCU: I3C Clock Frequency: %u MHz\n", clk_freq);

    switch (clk_freq) {
        case 160:
            //-- for 160 MHz
            write_i3c_socmgmtif_registers(0x00000002, 0x00000002, 0x00000003, 0x00000001);
            break;
        case 400:
            //-- for 400 MHz
            write_i3c_socmgmtif_registers(0x00000005, 0x00000005, 0x00000006, 0x00000002);
            break;
        case 500:
            //-- for 500 MHz
            write_i3c_socmgmtif_registers(0x00000006, 0x00000006, 0x00000007, 0x00000003);
            break;
        case 1000:
            //-- for 1000 MHz
            write_i3c_socmgmtif_registers(0x00000000, 0x00000000, 0x00000000, 0x00000000);
            break;
        default:
            VPRINTF(LOW, "Error: Unsupported clock frequency %u MHz\n", clk_freq);
            return;
    }

    //-- Enable the I3C bus
    VPRINTF(LOW, "MCU:  writing I3CCSR_I3CBASE_HC_CONTROL_BUS_ENABLE_LOW register  \n");
    i3c_reg_data = lsu_read_32( SOC_I3CCSR_I3CBASE_HC_CONTROL);
    i3c_reg_data = 1 << I3CCSR_I3CBASE_HC_CONTROL_BUS_ENABLE_LOW | i3c_reg_data;
    lsu_write_32( SOC_I3CCSR_I3CBASE_HC_CONTROL, i3c_reg_data);
}

// -- function boot i3c core (i3c bringup)
void boot_i3c_core(void) {

    VPRINTF(LOW, "MCU: I3C Core Bringup .. Started \n");
    boot_i3c_socmgmt_if();
    boot_i3c_standby_ctrl_mode(); 
    boot_i3c_reg();

}

// -- function to boot_mcu_with_fuses
void boot_mcu(){

    enum boot_fsm_state_e boot_fsm_ps;
    const uint32_t mbox_dlen = 64;
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
    uint32_t mbox_resp_data;
    uint32_t cptra_boot_go;
    uint32_t reg_data_32;
    
    mcu_mci_boot_go();

    ////////////////////////////////////
    // Fuse and Boot Bringup
    //
    // Wait for ready_for_fuses
    while(!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK));

    // Add fuse values
    // SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_0..11
    // Old : 53845724676e5e2f649d2c018e25c4fb80c2c28fcb6d6e93fb7cf908930a9953a9c69c3383aea9fd5573cb3db1ae0c3b
    // ROM7 : 9edb99809108c53f602883fe691943210445970d3d3d7eda4d320cc94113df3ab9d8a9741f7231851b866a64f75108e8
    // ROM11 : 8af1e8fbb74c19b9d6b234fe4dfc403a378cb4d5dd5cf4f375fb4ecc1d03f40071a3c8471c27f02db1b296f2cb3fb923
    reg_data_32 = 0x8af1e8fb; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_0, reg_data_32);
    reg_data_32 = 0xb74c19b9; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_1, reg_data_32);
    reg_data_32 = 0xd6b234fe; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_2, reg_data_32);
    reg_data_32 = 0x4dfc403a; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_6, reg_data_32);
    reg_data_32 = 0x1d03f400; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_7, reg_data_32);
    reg_data_32 = 0x71a3c847; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_8, reg_data_32);
    reg_data_32 = 0x1c27f02d; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_9, reg_data_32);
    reg_data_32 = 0xb1b296f2; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_10, reg_data_32);
    reg_data_32 = 0xcb3fb923; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_11, reg_data_32);

    // SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_0..11 
    // Old : 421275a87a71acf434b4f1076acdd68377d0a315f9e2a29b26b398913e89ff33006c10dcc4f1bd7467f1e2c41b0a893a
    // ROM7 : 879d4deca00dbddc5755ebc2ba1f40fa2626c033f5b2a02ac8ac032074baebc8adcbbc0c96d9d14061ea01aaa4902e75
    // ROM11 : 18211dda96dc39ae5782ef97408cad8da81915087739d3eeda8581a4d4a72c16df1e4144cbf6423e1bb98990153def5b
    reg_data_32 = 0x18211dda; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_0, reg_data_32);
    reg_data_32 = 0x96dc39ae; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_1, reg_data_32);
    reg_data_32 = 0x5782ef97; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_2, reg_data_32);
    reg_data_32 = 0x408cad8d; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_3, reg_data_32);
    reg_data_32 = 0xa8191508; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_4, reg_data_32);
    reg_data_32 = 0x7739d3ee; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_5, reg_data_32);
    reg_data_32 = 0xda8581a4; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_6, reg_data_32);
    reg_data_32 = 0xd4a72c16; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_7, reg_data_32);
    reg_data_32 = 0xdf1e4144; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_8, reg_data_32);
    reg_data_32 = 0xcbf6423e; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_9, reg_data_32);
    reg_data_32 = 0x1bb98990; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_10, reg_data_32);
    reg_data_32 = 0x153def5b; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_11, reg_data_32);

    // SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0..23
    reg_data_32 = 0x0;        lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0,      reg_data_32);
    reg_data_32 = 0xFFFFFFFF; lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_11,     reg_data_32);
    reg_data_32 = 0x02020101; lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_12,     reg_data_32);
    reg_data_32 = 0x30304040; lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_13,     reg_data_32);
    reg_data_32 = 0x05050606; lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_14,     reg_data_32);
    reg_data_32 = 0x70708080; lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_15,     reg_data_32);

    // -- Updating REVOCATIONS for MLDSA, LMS, ECC
    reg_data_32 = 0x0;        lsu_write_32(SOC_SOC_IFC_REG_FUSE_MLDSA_REVOCATION,        reg_data_32);
    reg_data_32 = 0x0;        lsu_write_32(SOC_SOC_IFC_REG_FUSE_LMS_REVOCATION,          reg_data_32);
    reg_data_32 = 0x0;        lsu_write_32(SOC_SOC_IFC_REG_FUSE_ECC_REVOCATION,          reg_data_32);

    // SOC_IFC_REG_FUSE_PQC_KEY_TYPE
    reg_data_32 = 0x1;        lsu_write_32(SOC_SOC_IFC_REG_FUSE_PQC_KEY_TYPE,        reg_data_32);

    // programming WDT 
    reg_data_32 = 1000;       lsu_write_32(SOC_SOC_IFC_REG_CPTRA_TIMER_CONFIG, reg_data_32);
    reg_data_32 = 250;        lsu_write_32(SOC_SOC_IFC_REG_CPTRA_WDT_CFG_1,reg_data_32);
    reg_data_32 = 1;          lsu_write_32(SOC_SOC_IFC_REG_CPTRA_WDT_CFG_0,reg_data_32);

    // Initialize fuses
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_FUSE_WR_DONE, SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
    VPRINTF(LOW, "MCU: Set fuse wr done\n");

    // Wait for Boot FSM to stall (on breakpoint) or finish bootup
    boot_fsm_ps = (lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK) >> SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW;
    while(boot_fsm_ps != BOOT_DONE && boot_fsm_ps != BOOT_WAIT) {
        for (uint8_t ii = 0; ii < 16; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
        boot_fsm_ps = (lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK) >> SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW;
    }

    // Advance from breakpoint, if set
    if (boot_fsm_ps == BOOT_WAIT) {
        lsu_write_32(SOC_SOC_IFC_REG_CPTRA_BOOTFSM_GO, SOC_IFC_REG_CPTRA_BOOTFSM_GO_GO_MASK);
    }
    VPRINTF(LOW, "MCU: Set BootFSM GO\n");

    ////////////////////////////////////
    // Mailbox command test
    //
    // MBOX: Wait for ready_for_mb_processing
    while(!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK)) {
        for (uint8_t ii = 0; ii < 16; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    }
    VPRINTF(LOW, "MCU: Ready for FW\n");

    // MBOX: Setup valid AXI USER
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0, 0xffffffff); // LSU AxUSER value. TODO: Derive from parameter
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_MASK);

    VPRINTF(LOW, "MCU: Configured MBOX Valid AXI USER\n");
 
}
