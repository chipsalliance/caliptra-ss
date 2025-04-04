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
    const uint32_t mbox_dlen = 10000; // Program to large value to make sure zeroization is still in progress when read of lock arrives

    uint32_t mbox_num = 0;
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
    mcu_mbox_clear_lock_out_of_reset(mbox_num);

    VPRINTF(LOW, "=================\nMCU MBOX SRAM Testing\n=================\n\n")

    // MBOX: Acquire lock
    while((lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK) & MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK));
    VPRINTF(LOW, "MCU: Mbox0 lock acquired\n");
    
    // MBOX: Write DLEN
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN, mbox_dlen);

    // MBOX: Execute
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE, MCU_MBOX0_CSR_MBOX_EXECUTE_EXECUTE_MASK);
    VPRINTF(LOW, "MCU: Mbox0 execute\n");

    // MBOX: Clear Execute
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE, 0);
    VPRINTF(LOW, "MCU: Mbox0 execute clear\n");

    // MBOX: Check that lock returns 1 while zeroize in progress
    if((lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK) & MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK) == 0) {
        VPRINTF(FATAL, "MCU: Mbox0 lock should have returned one while zeroize in progress\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    VPRINTF(LOW, "MCU: Mbox0 lock returned 1 while zeroing\n");

    SEND_STDOUT_CTRL(0xff);
}
