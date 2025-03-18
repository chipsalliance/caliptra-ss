
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

    // MBOX: Setup valid AXI USER
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_0, 0xffffffff);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_1, 1);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_2, 2);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_3, 3);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_0, MCI_REG_MBOX0_AXI_USER_LOCK_0_LOCK_MASK);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1_LOCK_MASK);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2_LOCK_MASK);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3_LOCK_MASK);
    VPRINTF(LOW, "MCU: Configured MBOX0 Valid AXI USER\n");

    VPRINTF(LOW, "=================\nMCU MBOX SRAM Testing\n=================\n\n")
    // MBOX: Acquire lock
    while((lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK) & MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK));
    VPRINTF(LOW, "MCU: Mbox0 lock acquired\n");
    
    // MBOX: Write DLEN
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN, mbox_dlen/2);

    // MBOX: Write SRAM
    for (uint32_t ii = 0; ii < (mbox_dlen/2)/4; ii++) {
        lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii), mbox_data[ii]);
    }

    // MBOX: Write DLEN again to simulate increasing the max dlen while lock is in place
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN, mbox_dlen);

    // MBOX: Write SRAM
    for (uint32_t ii = (mbox_dlen/2)/4; ii < mbox_dlen/4; ii++) {
        lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii), mbox_data[ii]);
    }

    // MBOX: check that some non-zero data has been written to beyond max_dlen/2
    if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(mbox_dlen/2)) == 0) {
        VPRINTF(FATAL, "MCU: Mbox0 should have valid non-zero data written here\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // MBOX: Write DLEN again to simulate decreasing the dlen while lock is in place to ensure max is retained
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN, mbox_dlen/2);

    // MBOX: Execute
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE, MCU_MBOX0_CSR_MBOX_EXECUTE_EXECUTE_MASK);
    VPRINTF(LOW, "MCU: Mbox0 execute\n");

    // MBOX: Clear Execute
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE, 0);
    VPRINTF(LOW, "MCU: Mbox0 execute clear\n");

    // MBOX: Re-acquire lock
    while((lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK) & MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK));
    VPRINTF(LOW, "MCU: Mbox0 lock acquired\n");

    // MBOX: check that data has been zeroed
    VPRINTF(LOW, "MCU: Checking that MCU Mbox0 up to max dlen had been zeroed \n");
    for (uint32_t ii = 0; ii < mbox_dlen/4; ii++) {
        if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii)) != 0) {
            VPRINTF(FATAL, "MCU: Mbox0 SRAM data not zeroed out at dword: %x\n", ii);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }

    SEND_STDOUT_CTRL(0xff);
}
