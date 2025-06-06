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
#include "caliptra_ss_lib.h"
#include "string.h"
#include "stdint.h"
#include "veer-csr.h"

#define STATUS_CHECK_LOOP_COUNT_FOR_RECOVERY 20

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
// volatile char* stdout = (char *)0xd0580000;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


void main (void) {

    int argc=0;
    char *argv[1];
    uint32_t i3c_reg_data;

    //-- Boot MCU
    VPRINTF(LOW, "MCU: Booting... \n");
    
    boot_mcu();
    boot_i3c_core();
    trigger_caliptra_go();
    mcu_cptra_user_init();
    wait_for_cptra_ready_for_mb_processing();

    VPRINTF(LOW, "MCU: Updating I3C Recovery Registers\n");
    // Programming I3C for Recovery Mode 
    // - DEVICE_STATUS_0
    i3c_reg_data = 0x00000003; // Recovery mode - ready to accept recovery image
    i3c_reg_data = 1 << 12 | i3c_reg_data; // Flashless/Streaming Boot (FSB) (Reason of recovery) 
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0, i3c_reg_data);

    // - RECOVERY_STATU_0
    i3c_reg_data = 0x00000001; // Awaiting recovery image
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS, i3c_reg_data);
    VPRINTF(LOW, "MCU: I3C Recovery Registers updated\n");
   
    //Halt the core to wait for Caliptra to finish the test
    csr_write_mpmc_halt();
}