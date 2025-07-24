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
//

/*
    Run this test with the following command
    submit_i ss_build -tc smoke_test_jtag_mcu_intent -op -to 250000
*/




#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


void main (void) {

    uint32_t cptra_boot_go;
    uint32_t read_data;

    // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring Caliptra out of reset 
    // This is just to see CSSBootFSM running correctly
    lsu_write_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, 1);
    VPRINTF(LOW, "MCU: Writing MCI SOC_MCI_TOP_MCI_REG_CALIPTRA_BOOT_GO\n");

    cptra_boot_go = lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO);
    VPRINTF(LOW, "MCU: Reading SOC_MCI_TOP_MCI_REG_CALIPTRA_BOOT_GO %x\n", cptra_boot_go);

    ////////////////////////////////////
    // Fuse and Boot Bringup
    //
    // Wait for ready_for_fuses
    while(!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK));
   
    //lcc_initialization();
    //transition_state(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);
    //reset_fc_lcc_rtl();

    // Initialize fuses
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_FUSE_WR_DONE, SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
    VPRINTF(LOW, "MCU: Set fuse wr done\n");

    for (uint16_t ii = 0; ii < 1000; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    //Write to the RO register to give them some value to read
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_FLOW_STATUS, 0x5a5a5a5a);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL, 0x5a5a5a5a);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_AGG_ERROR_FATAL, 0x5a5a5a5a);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_HW_ERROR_NON_FATAL, 0x5a5a5a5a);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_AGG_ERROR_NON_FATAL, 0x5a5a5a5a);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_ERROR_FATAL, 0x5a5a5a5a);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_ERROR_NON_FATAL, 0x5a5a5a5a);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_HW_ERROR_ENC, 0x5a5a5a5a);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_ERROR_ENC, 0x5a5a5a5a);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_0, 0x5a5a5a5a);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_1, 0x5a5a5a5a);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_2, 0x5a5a5a5a);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_3, 0x5a5a5a5a);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_4, 0x5a5a5a5a);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_5, 0x5a5a5a5a);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_6, 0x5a5a5a5a);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_7, 0x5a5a5a5a);


    //Sync phrase for JTAG
    VPRINTF(LOW, "=================\n CALIPTRA_SS JTAG MCU Smoke Test with ROM \n=================\n\n");
    
    read_data = 0;
    VPRINTF(LOW, "MCU: waits in loop until JTAG done\n");
    while(read_data != 0x1){
        read_data = lsu_read_32(SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO);
        for (uint32_t ii = 0; ii < 500; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    }

    VPRINTF(LOW, "MCU: JTAG work is done\n");
    SEND_STDOUT_CTRL(0xff);

}
