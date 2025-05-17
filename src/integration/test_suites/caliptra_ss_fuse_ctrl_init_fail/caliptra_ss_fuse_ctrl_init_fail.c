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

void init_fail() {
    const uint32_t faults[2] = {
        CMD_FC_LCC_CORRECTABLE_FAULT,
        CMD_FC_LCC_UNCORRECTABLE_FAULT
    };

    // Collect all buffered partitions with ECC enabled. Their content
    // will be read out after bringup which will trigger the ECC errors.
    partition_t part_sel[NUM_PARTITIONS];

    uint32_t count = 0;
    for (int i = 0; i < NUM_PARTITIONS; i++) {
        if (partitions[i].variant == 0 && partitions[i].has_ecc) {
            part_sel[count++] = partitions[i];
        }
    } 

    partition_t partition = part_sel[xorshift32() % count];
    uint32_t fault = faults[xorshift32() % 2];

    if (partition.address > 0x40 && partition.address < 0xD0) {
        grant_caliptra_core_for_fc_writes();
    } else {
        grant_mcu_for_fc_writes();
    }

    // Write one word in the selected partition and lock it afterwards.
    dai_wr(partition.address, 0x1, 0x2, partition.granularity, 0);
    calculate_digest(partition.address);

    // Inject either a correctable or uncorrectable error into the written partition.
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, fault);
    wait_dai_op_idle(0);

    reset_fc_lcc_rtl();
    wait_dai_op_idle(
        fault == CMD_FC_LCC_CORRECTABLE_FAULT ? 1 << partition.index : 0x3FFFF
    );

    uint32_t err_reg = lsu_read_32(SOC_OTP_CTRL_ERR_CODE_RF_ERR_CODE_0 + 0x4*partition.index);
    uint32_t status_reg = lsu_read_32(SOC_OTP_CTRL_STATUS);

    if (fault == CMD_FC_LCC_CORRECTABLE_FAULT) {
        if (err_reg != 0x2) {
            VPRINTF(LOW, "ERROR: err code register does not show correctable error: %08X\n", err_reg);
            return;
        }
    } else {
        if (err_reg != 0x3) {
            VPRINTF(LOW, "ERROR: err code register does not show uncorrectable error: %08X\n", err_reg);
            return;
        }
    }
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    transition_state(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);
    wait_dai_op_idle(0);

    initialize_otp_controller();

    init_fail();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
