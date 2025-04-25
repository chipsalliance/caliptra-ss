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

static const uint32_t manuf_token_hash[4] = {
    // Hash of token 0x00000001000000010000000100000001
    0x7381bd54, 0x32ac874c, 0x725373ec, 0xd10ceca9
};
static const uint32_t prod_token_hash[4] = {
    // Hash of token 0x00000002000000020000000200000002
    0xaeebc767, 0x5d3667f5, 0xda705018, 0xf1c0bd8a
};

typedef struct {
    uint32_t address;
    uint32_t granularity;
    lc_state_dec_t lc_state;
} prod_manuf_partition_t;

static const prod_manuf_partition_t partitions[12] = {
    { .address = 0x000, .granularity = 64, .lc_state = MANUF }, // SECRET_TEST_UNLOCK_PARTITION
    { .address = 0x048, .granularity = 64, .lc_state = MANUF }, // SECRET_MANUF_PARTITION
    { .address = 0x090, .granularity = 64, .lc_state = PROD  }, // SECRET_PROD_PARTITION_0
    { .address = 0x0A0, .granularity = 64, .lc_state = PROD  }, // SECRET_PROD_PARTITION_1
    { .address = 0x0B0, .granularity = 64, .lc_state = PROD  }, // SECRET_PROD_PARTITION_2
    { .address = 0x0C0, .granularity = 64, .lc_state = PROD  }, // SECRET_PROD_PARTITION_3
    { .address = 0x0D0, .granularity = 32, .lc_state = MANUF }, // SW_MANUF_PARTITION
    { .address = 0x5E0, .granularity = 32, .lc_state = MANUF }, // VENDOR_HASHES_MANUF_PARTITION
    { .address = 0x620, .granularity = 32, .lc_state = PROD },  // VENDOR_HASHES_PROD_PARTITION
    { .address = 0x910, .granularity = 32, .lc_state = PROD },  // VENDOR_REVOCATIONS_PROD_PARTITION
    { .address = 0x9A8, .granularity = 64, .lc_state = PROD },  // VENDOR_SECRET_PROD_PARTITION
    { .address = 0xBB0, .granularity = 64, .lc_state = PROD },  // VENDOR_NON_SECRET_PROD_PARTITION
};

/**
 * This function advances to the MANUF LC state and checks that all the
 * MANUF and PROD partitions are writable. It then progresses to the PROD
 * state where writes to MANUF partitions should be rejected.
 */
void manuf_prod_provision() {

    // 0x540: CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN
    const uint32_t base_address  = 0x4C0;
    const uint32_t manuf_token_address = 0x530;
    const uint32_t prod_token_address = 0x540;

    dai_wr(manuf_token_address, manuf_token_hash[0], manuf_token_hash[1], 64, 0);
    dai_wr(manuf_token_address + 0x08, manuf_token_hash[2], manuf_token_hash[3], 64, 0);
    dai_wr(prod_token_address, prod_token_hash[0], prod_token_hash[1], 64, 0);
    dai_wr(prod_token_address + 0x08, prod_token_hash[2], prod_token_hash[3], 64, 0);

    calculate_digest(base_address);

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Transition from TEST_UNLOCKED0 to MANUF
    transition_state(MANUF, 0x1, 0x1, 0x1, 0x1, 1);
    wait_dai_op_idle(0);

    uint32_t act_state = lsu_read_32(LC_CTRL_LC_STATE_OFFSET);
    uint32_t exp_state = calc_lc_state_mnemonic(MANUF);
    if (act_state != exp_state) {
        VPRINTF(LOW, "ERROR: incorrect state: exp: %08X, act: %08X\n", act_state, exp_state);
        exit(1);
    }

    // Check that all the MANUF and PROD partitionss are writeable.
    for (uint32_t i = 0; i < 12; i++) {
        if (partitions[i].address <= 0x80) {
            grant_caliptra_core_for_fc_writes();
        } else {
            grant_mcu_for_fc_writes(); 
        }
        dai_wr(partitions[i].address, i, 0, partitions[i].granularity, 0);
    }

    // Transition from MANUF to PROD.
    transition_state(PROD, 0x2, 0x2, 0x2, 0x2, 1);
    wait_dai_op_idle(0);

    act_state = lsu_read_32(LC_CTRL_LC_STATE_OFFSET);
    exp_state = calc_lc_state_mnemonic(PROD);
    if (act_state != exp_state) {
        VPRINTF(LOW, "ERROR: incorrect state: exp: %08X, act: %08X\n", act_state, exp_state);
        exit(1);
    }

    // Check that only PROD partitions are writeable and writes to MANUF partitions are blocked.
    for (uint32_t i = 0; i < 12; i++) {
        if (partitions[i].address <= 0x80) {
            grant_caliptra_core_for_fc_writes();
        } else {
            grant_mcu_for_fc_writes(); 
        }
        dai_wr(partitions[i].address, i, 0, partitions[i].granularity, partitions[i].lc_state == MANUF ? OTP_CTRL_STATUS_DAI_ERROR_MASK : 0);
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

    manuf_prod_provision();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
