
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
    uint32_t reg_data;
    uint32_t sram_data;

    VPRINTF(LOW, "=================\nMCU: Subsytem Bringup Test\n=================\n\n")
    mcu_mci_boot_go();
    

    VPRINTF(LOW, "MCU: Caliptra bringup\n")

    mcu_cptra_fuse_init();

    ////////////////////////////////////
    // Mailbox command test
    //

    mcu_cptra_poll_mb_ready();
    mcu_cptra_user_init();
    mcu_cptra_mbox_cmd();
    
    reg_data = lsu_read_32(SOC_MCI_TOP_MCI_REG_HW_REV_ID);
    VPRINTF(LOW, "MCU: MCI SOC_MCI_TOP_MCI_REG_HW_REV_ID %x\n", reg_data);
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
