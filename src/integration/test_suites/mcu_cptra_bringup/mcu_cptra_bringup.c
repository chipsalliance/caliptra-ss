
//********************************************************************************
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
//********************************************************************************

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include <string.h>
#include <stdint.h>

// volatile char* stdout = (char *)0xd0580000;
volatile char* stdout = (char *)0x21000410;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main (void) {
    int argc=0;
    char *argv[1];
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
    uint32_t mci_boot_fsm_go;
    uint32_t sram_data;

    VPRINTF(LOW, "=================\nMCU Boot FSM Go\n=================\n\n")
    
    // writing SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO register of MCI for CPTRA Boot FSM to bring Caliptra out of reset
    lsu_write_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, 1);
    VPRINTF(LOW, "MCU: Writing MCI SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO\n");

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
    
    mbox_resp_data = lsu_read_32(SOC_MCI_TOP_MCI_REG_HW_REV_ID);
    VPRINTF(LOW, "MCU: MCI SOC_MCI_TOP_MCI_REG_HW_REV_ID %x\n", mbox_resp_data);
    // lsu_write_32(0x21200000, 0x12345678);
    // VPRINTF(LOW, "MCU: I3C 0x2120_0000 write completed\n");
    // lsu_write_32(0x21200004, 0xABCDABCD);
    // VPRINTF(LOW, "MCU: I3C 0x2120_0004 write completed\n");
    // lsu_write_32(0x21203FFC, 0xDEADDEAD);
    // VPRINTF(LOW, "MCU: I3C 0x2120_03FC write completed\n");

    // mbox_resp_data = lsu_read_32(0x21200000);
    // VPRINTF(LOW, "MCU: I3C 0x2120_0000 %x\n", mbox_resp_data);
    // mbox_resp_data = lsu_read_32(0x21200004);
    // VPRINTF(LOW, "MCU: I3C 0x2120_0004 %x\n", mbox_resp_data);
    // mbox_resp_data = lsu_read_32(0x21203FFC);
    // VPRINTF(LOW, "MCU: I3C 0x2120_03FC %x\n", mbox_resp_data);

    // mbox_resp_dlen = lsu_read_32(I3CCSR_I3CBASE_CONTROLLER_DEVICE_ADDR);
    // VPRINTF(LOW, "MCU: I3C I3CCSR_I3CBASE_CONTROLLER_DEVICE_ADDR %x\n", mbox_resp_dlen);

    // lsu_write_32(SOC_I3CCSR_I3CBASE_HC_CONTROL, 0x12345678);
    // VPRINTF(LOW, "MCU: I3C SOC_I3CCSR_I3CBASE_HC_CONTROL write completed\n");

    // MBOX: Clear Execute
    lsu_write_32(SOC_MBOX_CSR_MBOX_EXECUTE, 0);
    VPRINTF(LOW, "MCU: Mbox execute clear\n");
    VPRINTF(LOW, "=================\nMCU SRAM Testing\n=================\n\n")
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_SRAM_EXEC_REGION_SIZE , 100);
    VPRINTF(LOW, "MCU: Configure EXEC REGION Size\n");
    
    lsu_write_32( (SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + 0x1000), 0xDEADBEEF);
    VPRINTF(LOW, "MCU: Writing to MCU SRAM\n");
    
    sram_data = lsu_read_32(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + 0x1000);
    if(sram_data == 0xDEADBEEF) {VPRINTF(LOW, "MCU: Read from MCU SRAM %x\n", sram_data);}
    else {VPRINTF(LOW, "MCU: Read from MCU SRAM failed %x\n", sram_data);}
    
    lsu_write_8( (SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + 0x1000), 0x00);
    VPRINTF(LOW, "MCU: Byte0 write to MCU SRAM\n");
    
    sram_data = lsu_read_32(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + 0x1000);
    if(sram_data == 0xDEADBE00) {VPRINTF(LOW, "MCU: Read from MCU SRAM %x\n", sram_data);}
    else {VPRINTF(LOW, "MCU: Read from MCU SRAM failed %x : Expected 0xDEADBE00\n", sram_data);}
    
    lsu_write_8( (SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + 0x1001), 0x00);
    VPRINTF(LOW, "MCU: Byte1 write to MCU SRAM\n");
    
    sram_data = lsu_read_32(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + 0x1000);
    if(sram_data == 0xDEAD0000) {VPRINTF(LOW, "MCU: Read from MCU SRAM %x\n", sram_data);}
    else {VPRINTF(LOW, "MCU: Read from MCU SRAM failed %x : Expected 0xDEAD0000\n", sram_data);}
    
    lsu_write_8( (SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + 0x1002), 0x00);
    VPRINTF(LOW, "MCU: Byte2 write to MCU SRAM\n");
    
    sram_data = lsu_read_32(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + 0x1000);
    if(sram_data == 0xDE000000) {VPRINTF(LOW, "MCU: Read from MCU SRAM %x\n", sram_data);}
    else {VPRINTF(LOW, "MCU: Read from MCU SRAM failed %x : Expected 0xDE000000\n", sram_data);}
    
    lsu_write_8( (SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + 0x1003), 0x00);
    VPRINTF(LOW, "MCU: Byte3 write to MCU SRAM\n");
    
    sram_data = lsu_read_32(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + 0x1000);
    if(sram_data == 0x00000000) {VPRINTF(LOW, "MCU: Read from MCU SRAM %x\n", sram_data);}
    else {VPRINTF(LOW, "MCU: Read from MCU SRAM failed %x : Expected 0x00000000\n", sram_data);}
    

    SEND_STDOUT_CTRL(0xff);

}
