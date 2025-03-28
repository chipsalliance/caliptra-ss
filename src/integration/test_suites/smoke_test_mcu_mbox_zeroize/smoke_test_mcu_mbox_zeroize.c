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

    VPRINTF(LOW, "=================\nMCU: Subsytem Bringup Test\n=================\n\n")
    mcu_mci_boot_go();
    

    VPRINTF(LOW, "MCU: Caliptra bringup\n")

    mcu_cptra_fuse_init();

    ////////////////////////////////////
    // Mailbox command test
    //

    mcu_cptra_poll_mb_ready();
    mcu_cptra_user_init();

    // MBOX: clear the lock on MBOX that is there from reset
    mcu_mbox_clear_lock_out_of_reset();

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
    VPRINTF(LOW, "MCU: Write data to Mbox0\n");

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
