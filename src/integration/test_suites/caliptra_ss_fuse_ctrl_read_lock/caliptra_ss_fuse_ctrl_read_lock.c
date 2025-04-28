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

#define NUM_READ_LOCK_PARTITIONS 7

void read_lock(void) {
    const uint32_t partition_addresses[NUM_READ_LOCK_PARTITIONS] = {
        0x00D0, // SW_MANUF_PARTITION
        0x2CD0, // SVN_PARTITION
        0x2CF8, // VENDOR_TEST_PARTITION
        0x2D38, // VENDOR_HASHES_MANUF_PARTITION
        0x2D78, // VENDOR_HASHES_PROD_PARTITION
        0x3068, // VENDOR_REVOCATIONS_PROD_PARTITION
        0x3308  // VENDOR_NON_SECRET_PROD_PARTITION
    };
    const uint32_t register_addresses[NUM_READ_LOCK_PARTITIONS] = {
        SOC_OTP_CTRL_SW_MANUF_PARTITION_READ_LOCK,
        SOC_OTP_CTRL_SVN_PARTITION_READ_LOCK,
        SOC_OTP_CTRL_VENDOR_TEST_PARTITION_READ_LOCK,
        SOC_OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_READ_LOCK,
        SOC_OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_READ_LOCK,
        SOC_OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK,
        SOC_OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK
    };
    // Try to read all the read-lockable partitions.
    uint32_t read_data[2];
    for (uint32_t i = 0; i < NUM_READ_LOCK_PARTITIONS; i++) {
        dai_rd(partition_addresses[i], &read_data[0], &read_data[1], 32, 0);
        lsu_write_32(register_addresses[i], 0x0);
        dai_rd(partition_addresses[i], &read_data[0], &read_data[1], 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    }
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    initialize_otp_controller();

    read_lock();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
