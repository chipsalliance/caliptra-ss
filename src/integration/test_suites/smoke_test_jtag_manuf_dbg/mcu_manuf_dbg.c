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
    submit_i ss_build -tc smoke_test_jtag_manuf_dbg -op -to 5000000
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
    uint32_t cptra_boot_go;

    uint32_t vector[16] = {
        0x9d2fee5e,
    0xd6ad3ab7,
    0xde49acb6,
    0x32afd8f2,
    0xc9cddd33,
    0xd5ed2846,
    0xc34b9649,
    0xb3a54fa3,
    0x67343f15,
    0x908277c6,
    0xc6779c52,
    0xfe55fd7d,
    0x96966232,
    0xcd03999d,
    0x90b3fae2,
    0x7f04e213
    };
    // VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");
    
    // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring Caliptra out of reset 
    // This is just to see CSSBootFSM running correctly
    mcu_cptra_init_d(.cfg_skip_set_fuse_done=true);

    ////////////////////////////////////
    // Fuse and Boot Bringup
    //
    // uint32_t base_address = SOC_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0;
    // for (int i = 0; i < 16; i++) {
    //     VPRINTF(LOW, "MCU: writing 0x%x to address of 0x%x\n", vector[i], base_address + (i * 4));
    //     lsu_write_32(base_address + (i * 4), vector[i]);
    // }


    for (uint32_t ii = 0; ii < 1000; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    VPRINTF(LOW, "=================\n CALIPTRA_SS JTAG MANUF DEBUG TEST with ROM \n=================\n\n");

    // Initialize fuses
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_FUSE_WR_DONE, SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
    VPRINTF(LOW, "MCU: Set fuse wr done\n");
    

    cptra_boot_go = 0;
    VPRINTF(LOW, "MCU: waits in success loop\n");
    while(cptra_boot_go != SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_MASK){
        cptra_boot_go = lsu_read_32(SOC_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP) & SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_MASK;
        for (uint32_t ii = 0; ii < 500; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    }

    VPRINTF(LOW, "MCU: Success done\n");
    //Give some time for jtag to test debug unlock success
    for (uint32_t ii = 0; ii < 10000; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }


    SEND_STDOUT_CTRL(0xff);

}
