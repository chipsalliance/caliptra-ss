
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
// Description: I3C Smoke test for Caliptra Subsystem
// Author     : Nilesh Patel
// Created    : 2025-01-14
// Comments   : 
//  This is a smoke test for I3C interface on Caliptra. 
//  The test brings up the I3C interface and sends a command to the I3C device. 
//  The test is expected to pass if the I3C device responds with the expected data.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "string.h"
#include "stdint.h"

#define STATUS_CHECK_LOOP_COUNT_FOR_RECOVERY 20

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
// volatile char* stdout = (char *)0xd0580000;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


// -- function to update various register to default values
// PROT_CAP, DEVICE_ID, HW_STATUS
void boot_i3c_recovery_reg(void) {

    uint32_t i3c_reg_data = 0x00000001;

    //-- PROT_CAP
    VPRINTF(LOW, "MCU: Updating I3C Recovery Registers\n");
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_0, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_1, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_2, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_3, i3c_reg_data++);

    //-- DEVICE_ID
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_0, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_1, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_2, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_3, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_4, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_5, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_6, i3c_reg_data++);

    //-- HW_STATUS
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS, i3c_reg_data++);

}

// -- function enable i3c recovery mode
// tb.reg_map.I3C_EC.SECFWRECOVERYIF.DEVICE_STATUS_0 = 0x03 
void enable_i3c_recovery_mode(void) {
    uint32_t i3c_reg_data;
    i3c_reg_data = 0x00000000;

    VPRINTF(LOW, "MCU: enable_i3c_recovery_mode register write \n");
    i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0);
    i3c_reg_data = 0x03 | i3c_reg_data;
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0, i3c_reg_data);
}

// -- function boot standby ctrl mode
// tb.reg_map.I3C_EC.STDBYCTRLMODE.STBY_CR_CONTROL.STBY_CR_ENABLE_INIT = 2
// tb.reg_map.I3C_EC.STDBYCTRLMODE.STBY_CR_CONTROL.TARGET_XACT_ENABLE = 1
void boot_standby_ctrl_mode(){
    uint32_t i3c_reg_data;
    i3c_reg_data = 0x00000000;

    VPRINTF(LOW, "MCU: boot_standby_ctrl_mode register writes \n");
    i3c_reg_data = lsu_read_32( SOC_I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL);
    i3c_reg_data = 2 << I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_STBY_CR_ENABLE_INIT_LOW | i3c_reg_data;
    i3c_reg_data = 1 << I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_TARGET_XACT_ENABLE_LOW | i3c_reg_data;
    lsu_write_32( SOC_I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL, i3c_reg_data);

    i3c_reg_data = lsu_read_32( SOC_I3CCSR_I3CBASE_HC_CONTROL);
    i3c_reg_data = 1 << I3CCSR_I3CBASE_HC_CONTROL_BUS_ENABLE_LOW | i3c_reg_data;
    lsu_write_32( SOC_I3CCSR_I3CBASE_HC_CONTROL, i3c_reg_data);

}

// -- function boot socmgmt_if
// tb.reg_map.I3C_EC.SOCMGMTIF.T_R_REG = 2
// tb.reg_map.I3C_EC.SOCMGMTIF.T_HD_DAT_REG = 10 
// tb.reg_map.I3C_EC.SOCMGMTIF.T_SU_DAT_REG =  10
// tb.reg_map.I3CBASE.HC_CONTROL.BUS_ENABLE = 1
void boot_socmgmt_if(void){
    uint32_t i3c_reg_data;
    VPRINTF(LOW, "MCU: boot_socmgmt_if register writes \n");
    i3c_reg_data = 0x00000002;
    lsu_write_32( SOC_I3CCSR_I3C_EC_SOCMGMTIF_T_R_REG, i3c_reg_data);
    i3c_reg_data = 0x0000000A;
    lsu_write_32( SOC_I3CCSR_I3C_EC_SOCMGMTIF_T_HD_DAT_REG , i3c_reg_data);
    i3c_reg_data = 0x0000000A;
    lsu_write_32( SOC_I3CCSR_I3C_EC_SOCMGMTIF_T_SU_DAT_REG, i3c_reg_data);
    i3c_reg_data = 0x00000000;
    i3c_reg_data = 1 << I3CCSR_I3CBASE_HC_CONTROL_BUS_ENABLE_LOW;
    lsu_write_32( SOC_I3CCSR_I3CBASE_HC_CONTROL, i3c_reg_data);
}

// -- function boot i3c core (i3c bringup)
void boot_i3c_core(void) {

    VPRINTF(LOW, "MCU: I3C Core Bringup .. Started \n");
    boot_socmgmt_if();
    boot_standby_ctrl_mode(); 
    boot_i3c_recovery_reg();

}

// -- function to boot mcu
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
    
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring Caliptra out of reset 
    // This is just to see CSSBootFSM running correctly
    lsu_write_32(SOC_MCI_TOP_MCI_REG_CALIPTRA_BOOT_GO, 1);
    VPRINTF(LOW, "MCU: Writing MCI SOC_MCI_TOP_MCI_REG_CALIPTRA_BOOT_GO\n");

    cptra_boot_go = lsu_read_32(SOC_MCI_TOP_MCI_REG_CALIPTRA_BOOT_GO);
    VPRINTF(LOW, "MCU: Reading SOC_MCI_TOP_MCI_REG_CALIPTRA_BOOT_GO %x\n", cptra_boot_go);

    VPRINTF(LOW, "=================\nMCU Caliptra Bringup\n=================\n\n")

    ////////////////////////////////////
    // Fuse and Boot Bringup
    //
    // Wait for ready_for_fuses
    while(!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK));

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
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0, 0xffffffff);
    //    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_1, 1);
    //    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_2, 2);
    //    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_3, 3);
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_MASK);
    //    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1_LOCK_MASK);
    //    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2_LOCK_MASK);
    //    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3_LOCK_MASK);
    VPRINTF(LOW, "MCU: Configured MBOX Valid AXI USER\n");

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
        for (uint8_t ii = 0; ii < 16; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
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

void main (void) {
    int argc=0;
    char *argv[1];
    uint32_t i3c_reg_data;

    boot_mcu();
    boot_i3c_core();

    //setting device address to 0x5A
    i3c_reg_data = 0x00000000;
    i3c_reg_data = 90 << 0  | i3c_reg_data;
    i3c_reg_data = 1  << 15 | i3c_reg_data;
    lsu_write_32( SOC_I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_ADDR, i3c_reg_data);

    //setting virtual device address to 0x5B
    i3c_reg_data = 0x00000000;
    i3c_reg_data = 91 << 0  | i3c_reg_data; //0x5B
    i3c_reg_data = 1  << 15 | i3c_reg_data;   
    lsu_write_32 ( SOC_I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRT_DEVICE_ADDR, i3c_reg_data);

    //  Enabling I3C Recovery Mode
    enable_i3c_recovery_mode();   

    for(uint8_t ii=0; ii<1; ii++) {

        VPRINTF(LOW, "MCU: Recovery Data Read.. %0d/04\n", ii);
        //setting device address to 0x5A
        for (uint16_t slp = 0; slp < 100; slp++) {

            //--nop
            for (uint8_t ii = 0; ii < 10; ii++) {
                __asm__ volatile ("nop");
            }
            VPRINTF(LOW, "MCU: Waiting for Recovery Data.. %0d\n", slp);
            i3c_reg_data = 0x00000000;
            i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_0);
            VPRINTF(LOW, "INDIRECT_FIFO_STATUS: %x\n", i3c_reg_data);
            if (i3c_reg_data == 0) {
                VPRINTF(LOW, "MCU: Recovery Data available\n");
                for (uint8_t ii = 0; ii < 16; ii++) {
                    __asm__ volatile ("nop");
                }
                break;
            }

        }
        // -- if recovery data is not available, 
        // -- return with error 0x1
        if (i3c_reg_data == 1) {
            VPRINTF(LOW, "MCU: Recovery Data not available\n");
            SEND_STDOUT_CTRL(0x01);
            return;
        }

        // -- 4 DWORDS of data read from FIFO
        for(uint8_t ii=0; ii<4; ii++) {
            i3c_reg_data = 0x00000000;
            i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_DATA);
            VPRINTF(LOW, "INDIRECT_FIFO_DATA: %x\n", i3c_reg_data);
        }

    }

    i3c_reg_data = 0x00000000;
    i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_0);
    VPRINTF(LOW, "INDIRECT_FIFO_status: %x\n", i3c_reg_data);

    // update recovery status register byte 0 with 0x03
    i3c_reg_data = 0x00000000;
    i3c_reg_data = 0x03 | i3c_reg_data;
    lsu_write_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS, i3c_reg_data);

    for(uint8_t ii=0; ii<100; ii++) {
        for (uint8_t ii = 0; ii < 16; ii++) {
            __asm__ volatile ("nop");
        }    
    }

    SEND_STDOUT_CTRL(0xff);
}




//-- Junk code
    // i3c_reg_data = 0x00000000;
    // i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_TTI_TX_DATA_PORT);
    // VPRINTF(LOW, "TTI TX DATA PORT: %x\n", i3c_reg_data);

    // i3c_reg_data = 0x00000000;
    // i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_TTI_RX_DATA_PORT);
    // VPRINTF(LOW, "TTI RX DATA PORT: %x\n", i3c_reg_data);
