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

void pk_volatile_lock(void) {
    const uint32_t prod_hash_addr[15] = {
        CPTRA_CORE_VENDOR_PK_HASH_1, CPTRA_CORE_VENDOR_PK_HASH_2,
        CPTRA_CORE_VENDOR_PK_HASH_3, CPTRA_CORE_VENDOR_PK_HASH_4,
        CPTRA_CORE_VENDOR_PK_HASH_5, CPTRA_CORE_VENDOR_PK_HASH_6,
        CPTRA_CORE_VENDOR_PK_HASH_7, CPTRA_CORE_VENDOR_PK_HASH_8,
        CPTRA_CORE_VENDOR_PK_HASH_9, CPTRA_CORE_VENDOR_PK_HASH_10,
        CPTRA_CORE_VENDOR_PK_HASH_11, CPTRA_CORE_VENDOR_PK_HASH_12,
        CPTRA_CORE_VENDOR_PK_HASH_13, CPTRA_CORE_VENDOR_PK_HASH_14,
        CPTRA_CORE_VENDOR_PK_HASH_15
    };
    uint32_t expected_lock = 0;

    for (uint32_t i = 0; i < 15; i++) {
        const uint32_t lock_mask = 1u << i;
        expected_lock |= lock_mask;

        // Prove lock bit i blocks writes to its hash: program 0x55555555, set
        // bit i (also engages the lock), attempt 0xAAAAAAAA, read back
        // 0x55555555. Bit i only locks prod_hash_addr[i], which is still virgin
        // and unlocked when the marker is programmed.
        if (!dai_lock_blocks_write(prod_hash_addr[i], 32,
                                   SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, lock_mask)) {
            handle_error("ERROR: locked PROD vendor PK hash was modified despite the volatile lock\n");
        }

        // The lock bits accumulate (W1S) and are sticky against a write of 0.
        if (lsu_read_32(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK) != expected_lock) {
            handle_error("ERROR: PROD PK volatile lock did not set expected bit-mask\n");
        }
        lsu_write_32(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, 0);
        if (lsu_read_32(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK) != expected_lock) {
            handle_error("ERROR: writing 0 cleared sticky PROD PK volatile lock bits\n");
        }
    }
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    initialize_otp_controller();

    pk_volatile_lock();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
