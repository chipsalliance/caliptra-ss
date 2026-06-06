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
 * Program production vendor PK hash fuses, then verify that volatile locks use
 * sticky per-bit mask semantics. Bit 2 locks CPTRA_CORE_VENDOR_PK_HASH_3 only.
 */
void program_vendor_hashes_prod_partition(void) {
    const uint32_t locked_hash = CPTRA_CORE_VENDOR_PK_HASH_3;
    const uint32_t unlocked_hash = CPTRA_CORE_VENDOR_PK_HASH_4;
    const uint32_t lock_mask = 1u << 2;
    const uint32_t data = 0xdeadbeef;

    if (!dai_wr(locked_hash, data, 0, 32, 0)) {
        handle_error("ERROR: initial write to PROD vendor PK hash 3 failed\n");
    }

    lsu_write_32(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, lock_mask);
    if (lsu_read_32(SOC_OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK) != lock_mask) {
        handle_error("ERROR: PROD PK volatile lock did not retain bit-mask value\n");
    }

    if (!dai_wr(unlocked_hash, data + 1, 0, 32, 0)) {
        handle_error("ERROR: unselected PROD vendor PK hash 4 was unexpectedly locked\n");
    }

    if (!dai_wr(locked_hash, data + 2, 0, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK)) {
        handle_error("ERROR: locked PROD vendor PK hash 3 write was not rejected\n");
    }
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
    
    lcc_initialization();
    // Set AXI user ID to MCU.
    grant_mcu_for_fc_writes(); 

    transition_state_check(TEST_UNLOCKED0, raw_unlock_token);

    initialize_otp_controller();

    program_vendor_hashes_prod_partition();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
