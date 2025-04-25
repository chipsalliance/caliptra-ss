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

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

typedef struct {
    uint32_t address;
    uint32_t digest_address;
    uint32_t index;
} partition_t;

// XXX: Fuse addresses, eventually these should be generated automatically.
// Buffered partitions.
static partition_t partitions[8] = {
    // SECRET_TEST_UNLOCK_PARTITION
    { .address = 0x000, .digest_address = 0x040, .index = 0 },
     // SECRET_MANUF_PARTITION
    { .address = 0x048, .digest_address = 0x088, .index = 1 },
    // SECRET_PROD_PARTITION_0
    { .address = 0x090, .digest_address = 0x098, .index = 2 },
    // SECRET_PROD_PARTITION_1 
    { .address = 0x0A0, .digest_address = 0x0A8, .index = 3 },
    // SECRET_PROD_PARTITION_2 
    { .address = 0x0B0, .digest_address = 0x0B8, .index = 4 },
    // SECRET_PROD_PARTITION_3
    { .address = 0x0C0, .digest_address = 0x0C8, .index = 5 },
    // SECRET_LC_TRANSITION_PARTITION
    { .address = 0x4C0, .digest_address = 0x570, .index = 7 },  
    // VENDOR_SECRET_PROD_PARTITION
    { .address = 0x9A8, .digest_address = 0xBA8, .index = 13 }
};

void init_fail() {
    const uint32_t faults[2] = {
        CMD_FC_LCC_CORRECTABLE_FAULT,
        CMD_FC_LCC_UNCORRECTABLE_FAULT
    };

    partition_t partition = partitions[xorshift32() % 8];
    uint32_t fault = faults[xorshift32() % 2];

    if (partition.address < 0x090) {
        grant_caliptra_core_for_fc_writes();
    } else {
        grant_mcu_for_fc_writes();
    }

    // Write one word in the selected partition and lock it afterwards.
    dai_wr(partition.address, 0x1, 0x2, 64, 0);
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
