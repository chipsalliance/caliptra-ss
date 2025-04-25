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
    uint32_t granularity;
} partition_t;

static const partition_t partitions[15] = {
    { .address = 0x000, .granularity = 64 }, // SECRET_TEST_UNLOCK_PARTITION
    { .address = 0x048, .granularity = 64 }, // SECRET_MANUF_PARTITION
    { .address = 0x090, .granularity = 64 }, // SECRET_PROD_PARTITION_0
    { .address = 0x0A0, .granularity = 64 }, // SECRET_PROD_PARTITION_1
    { .address = 0x0B0, .granularity = 64 }, // SECRET_PROD_PARTITION_2
    { .address = 0x0C0, .granularity = 64 }, // SECRET_PROD_PARTITION_3
    { .address = 0x0D0, .granularity = 32 }, // SW_MANUF_PARTITION
    { .address = 0x4C0, .granularity = 64 }, // SECRET_LC_TRANSITION_PARTITION
    { .address = 0x578, .granularity = 32 }, // SVN_PARTITION
    { .address = 0x5A0, .granularity = 32 }, // VENDOR_TEST
    { .address = 0x5A0, .granularity = 32 }, // VENDOR_HASHES_MANUF_PARTITION
    { .address = 0x620, .granularity = 32 }, // VENDOR_HASHES_PROD_PARTITION
    { .address = 0x910, .granularity = 32 }, // VENDOR_REVOCATIONS_PROD_PARTITION
    { .address = 0x9A8, .granularity = 64 }, // VENDOR_SECRET_PROD_PARTITION
    { .address = 0xBB0, .granularity = 64 }  // VENDOR_NON_SECRET_PROD_PARTITION
};

/**
 * This test performs DAI writes over the AXI bus on the boundaries of the
 * fuse controller access table entries with randomized fuse writes and
 * random AXI user ids.
 */
void axi_id() {
    const uint32_t sentinel = 0xAB;

    partition_t partition;
    uint32_t axi_user;

    for (int i = 0; i < 4; i++) {
        partition = partitions[xorshift32() % 15];
        axi_user = xorshift32() % 2;
        
        if (axi_user) {
            grant_mcu_for_fc_writes();
        } else {
            grant_caliptra_core_for_fc_writes();
        }

        // Both CPTRA_CORE_MANUF_DEBUG_UNLOCK_TOKEN and CPTRA_CORE_UDS_SEED must not
        // be modified by the AXI requests stemming from the MCU.
        if (partition.address < 0x090 && axi_user) {
            dai_wr(partition.address, sentinel, sentinel, partition.granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK);
        } else {
            dai_wr(partition.address, sentinel, sentinel, partition.granularity, 0);
        }
    }
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    transition_state_check(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);

    initialize_otp_controller();

    axi_id();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
