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
static uint32_t _addr6[] = { 0x0D0, 0x0D1, 0x131, 0x141, 0x143, 0x173, 0x1A3, 0x1D3, 0x203, 0x233, 0x263, 0x293 };
static uint32_t _addr7[] = { 0x4C0, 0x4D0, 0x4E0, 0x4F0, 0x500, 0x510, 0x520, 0x530, 0x540, 0x550, 0x560 };
static uint32_t _addr8[] = { 0x5E0, 0x610 };
static uint32_t _addr9[] = { 
    0x620, 0x650, 0x651, 0x681, 0x682, 0x6B2, 0x6B3, 0x6E3, 0x6E4, 0x714, 0x715, 0x745,
    0x746, 0x776, 0x777, 0x7A7, 0x7A8, 0x7D8, 0x7D9, 0x809, 0x80A, 0x83A, 0x83B, 0x86B,
    0x86C, 0x89C, 0x89D, 0x8CD, 0x8CE, 0x8FE, 0x8FF
};
static uint32_t _addr10[] = { 
    0x910, 0x911, 0x915, 0x919, 0x91A, 0x91E, 0x922, 0x923, 0x927, 0x92B, 0x92C, 0x930,
    0x934, 0x935, 0x939, 0x93D, 0x942, 0x946, 0x947, 0x94B, 0x94F, 0x950, 0x954, 0x958,
    0x959, 0x95D, 0x961, 0x962, 0x966, 0x96A, 0x96B, 0x96F, 0x973, 0x974, 0x978, 0x97C,
    0x97D, 0x981, 0x985, 0x986, 0x98A, 0x98E, 0x98F, 0x993, 0x997, 0x998, 0x99C
};
static uint32_t _addr11[] = { 
    0x9A8, 0x9C8, 0x9E8, 0xA08, 0xA28, 0xA48, 0xA68, 0xA88, 0xAA8, 0xAC8, 0xAE8, 0xB08,
    0xB28, 0xB48, 0xB68, 0xB88
};
static uint32_t _addr12[] = { 
    0xBB0, 0xBD0, 0xBF0, 0xC10, 0xC30, 0xC50, 0xC70, 0xC90, 0xCB0, 0xCD0, 0xCF0, 0xD10,
    0xD30, 0xD50, 0xD70, 0xD90
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
    { .address = 0x0D0, .granularity = 32, .is_software = true,  .num_fuses = 5,  .fuse_addresses = _addr6, .digest_address = 0x4B8 }, 
    // SECRET_LC_TRANSITION_PARTITION
    { .address = 0x4C0, .granularity = 64, .is_software = false, .num_fuses = 11, .fuse_addresses = _addr7, .digest_address = 0x570 },  
    // VENDOR_HASHES_MANUF_PARTITION
    { .address = 0x5E0, .granularity = 32, .is_software = true,  .num_fuses = 2,  .fuse_addresses = _addr8, .digest_address = 0x618 }, 
    // VENDOR_HASHES_PROD_PARTITION
    { .address = 0x620, .granularity = 32, .is_software = true,  .num_fuses = 31, .fuse_addresses = _addr9, .digest_address = 0x908 }, 
    // VENDOR_REVOCATIONS_PROD_PARTITION
    { .address = 0x910, .granularity = 32, .is_software = true,  .num_fuses = 48, .fuse_addresses = _addr10, .digest_address = 0x9A0 }, 
    // VENDOR_SECRET_PROD_PARTITION
    { .address = 0x9A8, .granularity = 64, .is_software = false, .num_fuses = 16, .fuse_addresses = _addr11, .digest_address = 0xBA8 },
    // VENDOR_NON_SECRET_PROD_PARTITION
    { .address = 0xBB0, .granularity = 64, .is_software = true,  .num_fuses = 16, .fuse_addresses = _addr12, .digest_address = 0xFA0 }, 
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
        if (partitions[i].address <= 0x80) {
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
        if (partitions[i].address <= 0x80) {
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
