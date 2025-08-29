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

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")

    mcu_cptra_init_d();
    wait_dai_op_idle(0);
    
    lcc_initialization();
    // Set AXI user ID to MCU.
    //grant_mcu_for_fc_writes(); 
    
    transition_state_check(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);
    
    initialize_otp_controller();

    const uint32_t base_address = CPTRA_CORE_MANUF_DEBUG_UNLOCK_TOKEN;
    const uint32_t fuse_address = base_address;
    const uint32_t digest_address = SW_TEST_UNLOCK_PARTITION_DIGEST;

    const uint32_t sentinel = 0xAB;

    uint32_t read_data[2];

    // Write debug unlock token
    dai_wr(fuse_address, sentinel, 0, 32, 0);

    // Read back and compare
    dai_rd(fuse_address, &read_data[0], &read_data[1], 32, 0);
    if (read_data[0] != sentinel) {
        VPRINTF(LOW, "ERROR: wrong debug unlock token\n");
        goto epilogue;
    }

    // Make sure digest field is 0.
    read_data[0] = lsu_read_32(SOC_OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_DIGEST_0);
    read_data[1] = lsu_read_32(SOC_OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_DIGEST_1);
    if (read_data[0] != 0x0 || read_data[1] != 0x0) {
        VPRINTF(LOW, "ERROR: digest is not zero\n");
        goto epilogue;
    }

    calculate_digest(base_address, 0);
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Make sure digest field is not 0.
    read_data[0] = lsu_read_32(SOC_OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_DIGEST_0);
    read_data[1] = lsu_read_32(SOC_OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_DIGEST_1);
    if (read_data[0] == 0x0 || read_data[1] == 0x0) {
        VPRINTF(LOW, "ERROR: digest is zero\n");
        goto epilogue;
    }

    // Read back and compare
    dai_rd(fuse_address, &read_data[0], &read_data[1], 32, 0);
    if (read_data[0] != sentinel) {
        VPRINTF(LOW, "ERROR: wrong debug unlock token\n");
    }

epilogue:
    for (uint8_t i = 0; i < 160; i++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}