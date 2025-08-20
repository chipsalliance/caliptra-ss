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
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"
#include "fuse_ctrl_mmap.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif




/**
 * This function goes through a fuse controller zeroization sequence
 * (using the input port and the LCC scrap state). This actual broadcast
 * signal cannot be observed in software and must be verified through assertions.
 */

void program_HEK() {

    partition_t hw_part = partitions[CPTRA_SS_LOCK_HEK_PROD_3];
    uint32_t base_address = partitions[CPTRA_SS_LOCK_HEK_PROD_3].address;
    uint32_t digest_address = partitions[CPTRA_SS_LOCK_HEK_PROD_3].digest_address;
    uint32_t fuse_address = base_address;
    VPRINTF(LOW, "MCU: Writing HEK SEED\n"); 
    int i;
    for (i = 0; i < 2; i++)
        dai_wr(fuse_address+i*4, 0x55AA55AA, 0, 32, 0);

    
    VPRINTF(LOW, "MCU: HEK SEED Write is done\n"); 
    VPRINTF(LOW, "MCU: FC is going to calculate the digest for HEK\n"); 
    calculate_digest(fuse_address);

    VPRINTF(LOW, "MCU: HEK SEED digest is done\n"); 
    reset_fc_lcc_rtl();
    uint32_t rdata0, rdata1;
    for (i = 0; i < 2; i++) {
        dai_rd(fuse_address+i*4, &rdata0, &rdata1, 32, 0);
        if (rdata0 != 0x55AA55AA) {
            VPRINTF(LOW, "MCU ERROR: HEK SEED is not written correctly! \n");
            return;
        }
        lsu_write_32(SOC_SOC_IFC_REG_FUSE_HEK_SEED_3+i*4, rdata0);
    }

}

void zeroize() {

    partition_t hw_part = partitions[CPTRA_SS_LOCK_HEK_PROD_3];
    uint32_t base_address = partitions[CPTRA_SS_LOCK_HEK_PROD_3].address;
    uint32_t digest_address = partitions[CPTRA_SS_LOCK_HEK_PROD_3].digest_address;
    uint32_t fuse_address = base_address;
    uint32_t data[2];

    dai_zer(fuse_address, &data[0], &data[1], hw_part.granularity, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: fuse is not zeroized\n");
        goto epilogue;
    }
    memset(data, 0, 2*sizeof(uint32_t));
    // Zeroize marker field.
    dai_zer(hw_part.zer_address, &data[0], &data[1], 64, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: digest is not zeroized\n");
        goto epilogue;
    }
    memset(data, 0, 2*sizeof(uint32_t));

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

epilogue:
    VPRINTF(LOW, "zeroization test finished\n");
}

void main (void) {

    partition_t hw_part = partitions[CPTRA_SS_LOCK_HEK_PROD_3];
    uint32_t base_address = partitions[CPTRA_SS_LOCK_HEK_PROD_3].address;
    uint32_t digest_address = partitions[CPTRA_SS_LOCK_HEK_PROD_3].digest_address;
    uint32_t fuse_address = base_address;


    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")

    // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring Caliptra out of reset 
    // This is just to see CSSBootFSM running correctly
    mcu_mci_boot_go();
    ////////////////////////////////////
    // Fuse and Boot Bringup
    //
    // Wait for ready_for_fuses
    while(!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK));

    
    mcu_cptra_init_d(.cfg_skip_set_fuse_done=true);
    // wait_dai_op_idle(0);
      
    // lcc_initialization();

    // transition_state(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);
    wait_dai_op_idle(0);

    initialize_otp_controller();


    program_HEK();

    // Initialize fuses
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_FUSE_WR_DONE, SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
    VPRINTF(LOW, "MCU: Set fuse wr done\n");  

    uint32_t cptra_boot_go;

    cptra_boot_go = 0;
    VPRINTF(LOW, "MCU: waits in success loop\n");
    while(cptra_boot_go != SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK){
        cptra_boot_go = lsu_read_32(SOC_SOC_IFC_REG_SS_OCP_LOCK_CTRL) & SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK;
        for (uint32_t ii = 0; ii < 500; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    }

    zeroize();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
