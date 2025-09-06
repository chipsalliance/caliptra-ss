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
#include <stdint.h>

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
const uint32_t testData[] = {0xA5A5A5A5, 0x96969696};

void program_HEK() {
    partition_t partition =  partitions[CPTRA_SS_LOCK_HEK_PROD_3];
    uint32_t fuse_address =  partition.address;

    // Programs racthet seed 
    VPRINTF(LOW, "MCU: Writing HEK SEED\n"); 
    for (uint32_t i = 0; i < 2; i++) {
        dai_wr(fuse_address+i*4, testData[0], testData[1], 32, 0);
    }
    VPRINTF(LOW, "MCU: HEK SEED Write is done\n"); 

    // VPRINTF(LOW, "MCU: FC is going to calculate the digest for HEK\n"); 
    // dai_wr(partition.digest_address, 0xFF, 0xFF, 32, 0);
    // wait_dai_op_idle(0);
    // calculate_digest(fuse_address, 0);
    VPRINTF(LOW, "MCU: HEK SEED digest is done\n"); 

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);
    uint32_t rdata[2] = {0x00, 0x00};
    for (uint32_t i = 0; i < 2; i++) {
        // Read the value back
        dai_rd(fuse_address+i*4, &rdata[0], &rdata[1], 32, 0);
        if (rdata[0] != testData[0]) {
            VPRINTF(LOW, "MCU ERROR: HEK SEED is not written correctly! Iteration %d, reads 0x%x 0x%x! \n",
                i, rdata[0], rdata[1]);
            return;
        }
        // Populates Caliptra-core's HEK_SEED registers with the read value
        lsu_write_32(SOC_SOC_IFC_REG_FUSE_HEK_SEED_3+i*4, rdata[0]);
    }
}

/*
 * Programs racthet seed and reads it;
 * Populates Caliptra-core's HEK_SEED registers with the read value;
 * Releases the caliptra core by setting CPTRA_FUSE_WR_DONE;
 * Wait for OCP_LOCK_PROGRESS;
 */
void main (void) {
    partition_t hw_part = partitions[CPTRA_SS_LOCK_HEK_PROD_3];
    uint32_t base_address = partitions[CPTRA_SS_LOCK_HEK_PROD_3].address;
    uint32_t fuse_address = base_address;

    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")

    // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring Caliptra out of reset 
    // This is just to see CSSBootFSM running correctly
    mcu_mci_boot_go();

    // Wait for ready_for_fuses
    while(!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK));
    
    mcu_cptra_init_d(.cfg_skip_set_fuse_done=true);
    wait_dai_op_idle(0);

    grant_mcu_for_fc_writes();
    initialize_otp_controller();

    program_HEK();

    // Releases the caliptra core by setting CPTRA_FUSE_WR_DONE;
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_FUSE_WR_DONE, SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
    VPRINTF(LOW, "MCU: Set fuse wr done\n");  

    uint32_t cptra_boot_go;

    // Wait for OCP_LOCK_PROGRESS;
    cptra_boot_go = 0;
    VPRINTF(LOW, "MCU: waits in success loop\n");
    while(cptra_boot_go != SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK){
        cptra_boot_go = lsu_read_32(SOC_SOC_IFC_REG_SS_OCP_LOCK_CTRL) & SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK;
        for (uint32_t ii = 0; ii < 500; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    }

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
