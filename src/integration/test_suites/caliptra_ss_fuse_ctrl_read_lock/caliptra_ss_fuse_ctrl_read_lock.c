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

void read_lock(void) {
    // Collect all read-lockable partitions.
    partition_t part_sel[NUM_PARTITIONS];

    uint32_t count = 0;
    for (int i = 0; i < NUM_PARTITIONS; i++) {
        if (partitions[i].has_read_lock) {
            part_sel[count++] = partitions[i];
        }
    } 

    const uint32_t register_addresses[] = {
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
    for (uint32_t i = 0; i < count; i++) {
        dai_rd(part_sel[i].address, &read_data[0], &read_data[1], part_sel[i].granularity, 0);
        lsu_write_32(register_addresses[i], 0x0);
        dai_rd(part_sel[i].address, &read_data[0], &read_data[1], part_sel[i].granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK);
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
