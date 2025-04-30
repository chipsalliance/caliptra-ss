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
#include <stdbool.h>

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

// XXX: Fuse addresses, eventually these should be generated automatically.
static uint32_t _addr0[] = { 0x000 };
static uint32_t _addr1[] = { 0x048 };
static uint32_t _addr2[] = { 0x090 };
static uint32_t _addr3[] = { 0x0A0 };
static uint32_t _addr4[] = { 0x0B0 };
static uint32_t _addr5[] = { 0x0C0 };
static uint32_t _addr6[] = { 0x0D0, 0x0D1, 0x1FE1, 0x1FF1, 0x1FF3, 0x2023, 0x2053, 0x2083, 0x20B3, 0x20E3, 0x2113, 0x2143 };
static uint32_t _addr7[] = { 0x2C18, 0x2C28, 0x2C38, 0x2C48, 0x2C58, 0x2C68, 0x2C78, 0x2C88, 0x2C98, 0x2CA8, 0x2CB8 };
static uint32_t _addr8[] = { 0x2D38, 0x2D68 };
static uint32_t _addr9[] = { 
    0x2D78, 0x2DA8, 0x2DA9, 0x2DD9, 0x2DDA, 0x2E0A, 0x2E0B, 0x2E3B, 0x2E3C, 0x2E6C, 0x2E6D, 0x2E9D,
    0x2E9E, 0x2ECE, 0x2ECF, 0x2EFF, 0x2F00, 0x2F30, 0x2F31, 0x2F61, 0x2F62, 0x2F92, 0x2F93, 0x2FC3,
    0x2FC4, 0x2FF4, 0x2FF5, 0x3025, 0x3026, 0x3056, 0x3057
};
static uint32_t _addr10[] = { 
    0x3068, 0x3069, 0x306D, 0x3071, 0x3072, 0x3076, 0x307A, 0x307B, 0x307F, 0x3083, 0x3084, 0x3088,
    0x308C, 0x308D, 0x3091, 0x3095, 0x3096, 0x309A, 0x309E, 0x309F, 0x30A3, 0x30A7, 0x30A8, 0x30AC,
    0x30B0, 0x30B1, 0x30B5, 0x30B9, 0x30BA, 0x30BE, 0x30C2, 0x30C3, 0x30C7, 0x30CB, 0x30CC, 0x30D0,
    0x30D4, 0x30D5, 0x30D9, 0x30DD, 0x30DE, 0x30E2, 0x30E6, 0x30E7, 0x30EB, 0x30EF, 0x30F0, 0x30F4
};
static uint32_t _addr11[] = { 
    0x3100, 0x3120, 0x3140, 0x3160, 0x3180, 0x31A0, 0x31C0, 0x31E0, 0x3200, 0x3220, 0x3240, 0x3260,
    0x3280, 0x32A0, 0x32C0, 0x32E0
};
static uint32_t _addr12[] = { 
    0x3308, 0x3328, 0x3348, 0x3368, 0x3388, 0x33A8, 0x33C8, 0x33E8, 0x3408, 0x3428, 0x3448,
    0x3468, 0x3488, 0x34A8, 0x34C8, 0x34E8
};

typedef struct {
    uint32_t address;
    uint32_t granularity;
    bool is_software;

    uint32_t num_fuses;
    uint32_t *fuse_addresses;
    uint32_t digest_address;
} partition_t;

// XXX: Fuse addresses, eventually these should be generated automatically.
static partition_t partitions[13] = {
    // SECRET_TEST_UNLOCK_PARTITION
    { .address = 0x000, .granularity = 64, .is_software = false, .num_fuses = 1,  .fuse_addresses = _addr0, .digest_address = 0x040 },
     // SECRET_MANUF_PARTITION
    { .address = 0x048, .granularity = 64, .is_software = false, .num_fuses = 1,  .fuse_addresses = _addr1, .digest_address = 0x088 },
    // SECRET_PROD_PARTITION_0
    { .address = 0x090, .granularity = 64, .is_software = false, .num_fuses = 1,  .fuse_addresses = _addr2, .digest_address = 0x098 },
    // SECRET_PROD_PARTITION_1 
    { .address = 0x0A0, .granularity = 64, .is_software = false, .num_fuses = 1,  .fuse_addresses = _addr3, .digest_address = 0x0A8 },
    // SECRET_PROD_PARTITION_2 
    { .address = 0x0B0, .granularity = 64, .is_software = false, .num_fuses = 1,  .fuse_addresses = _addr4, .digest_address = 0x0B8 },
    // SECRET_PROD_PARTITION_3
    { .address = 0x0C0, .granularity = 64, .is_software = false, .num_fuses = 1,  .fuse_addresses = _addr5, .digest_address = 0x0C8 },
    // SW_MANUF_PARTITION
    { .address = 0x0D0, .granularity = 32, .is_software = true,  .num_fuses = 5,  .fuse_addresses = _addr6, .digest_address = 0x2C10 }, 
    // SECRET_LC_TRANSITION_PARTITION
    { .address = 0x2C18, .granularity = 64, .is_software = false, .num_fuses = 11, .fuse_addresses = _addr7, .digest_address = 0x2CC8 },  
    // VENDOR_HASHES_MANUF_PARTITION
    { .address = 0x2D38, .granularity = 32, .is_software = true,  .num_fuses = 2,  .fuse_addresses = _addr8, .digest_address = 0x2D70 }, 
    // VENDOR_HASHES_PROD_PARTITION
    { .address = 0x2D78, .granularity = 32, .is_software = true,  .num_fuses = 31, .fuse_addresses = _addr9, .digest_address = 0x3060 }, 
    // VENDOR_REVOCATIONS_PROD_PARTITION
    { .address = 0x3068, .granularity = 32, .is_software = true,  .num_fuses = 48, .fuse_addresses = _addr10, .digest_address = 0x30F8 }, 
    // VENDOR_SECRET_PROD_PARTITION
    { .address = 0x3100, .granularity = 64, .is_software = false, .num_fuses = 16, .fuse_addresses = _addr11, .digest_address = 0x3300 },
    // VENDOR_NON_SECRET_PROD_PARTITION
    { .address = 0x3308, .granularity = 64, .is_software = true,  .num_fuses = 16, .fuse_addresses = _addr12, .digest_address = 0x3FA0 }, 
};

void test_unlocked0_provision() {
    const uint32_t sentinel = 0xA5;

    uint32_t act_state = lsu_read_32(LC_CTRL_LC_STATE_OFFSET);
    uint32_t exp_state = calc_lc_state_mnemonic(TEST_UNLOCKED0);
    if (act_state != exp_state) {
        VPRINTF(LOW, "ERROR: incorrect state: exp: %08X, act: %08X\n", act_state, exp_state);
        exit(1);
    }

    uint32_t read_value, zero;
    uint32_t rnd_fuse_addresses[13];

    for (uint32_t i = 0; i < 13; i++) {
        if (partitions[i].address > 0x40 && partitions[i].address < 0xD0) {
            grant_caliptra_core_for_fc_writes();
        } else {
            grant_mcu_for_fc_writes(); 
        }

        rnd_fuse_addresses[i] = partitions[i].fuse_addresses[xorshift32() % partitions[i].num_fuses];
        
        dai_wr(rnd_fuse_addresses[i], sentinel, 0, partitions[i].granularity, 0);
        
        dai_rd(rnd_fuse_addresses[i], &read_value, &zero, partitions[i].granularity, 0);
        if ((read_value & 0xFF) != sentinel) {
            VPRINTF(LOW, "ERROR: incorrect value: exp: %08X act: %08X\n", read_value, sentinel);
        }

        if (partitions[i].is_software) {
            dai_wr(partitions[i].digest_address, sentinel, 0, 64, 0);
        } else {
            calculate_digest(partitions[i].address);
        }
    } 

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    for (uint32_t i = 0; i < 13; i++) {
        if (partitions[i].address > 0x40 && partitions[i].address < 0xD0) {
            grant_caliptra_core_for_fc_writes();
        } else {
            grant_mcu_for_fc_writes(); 
        }

        dai_wr(rnd_fuse_addresses[i], sentinel, 0, partitions[i].granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK);
        
        if (partitions[i].is_software) {
            dai_rd(rnd_fuse_addresses[i], &read_value, &zero, partitions[i].granularity, 0);
            if ((read_value & 0xFF) != sentinel) {
                VPRINTF(LOW, "ERROR: incorrect value: exp: %08X act: %08X\n", read_value, sentinel);
            }
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

    test_unlocked0_provision();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
