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
#include "fuse_ctrl_read_lock_map.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void read_lock(void) {
    // For each partition with a read-lock CSR:
    //
    //    - Read from the partition (this should succeed)
    //    - Clear that read-lock
    //    - Read again from the partition (this should fail with a DAI error)
    uint32_t read_data[2];
    for (int lockable_idx = 0; ; lockable_idx++) {
        uint32_t partition_idx = read_lock_partition_indices[lockable_idx];
        if (partition_idx == UINT32_MAX) break;

        const partition_t *partition = &partitions[partition_idx];
        dai_rd(partition->address, &read_data[0], &read_data[1], partition->granularity, 0);
        lsu_write_32(read_lock_csr_mapping[lockable_idx], 0x0);
        dai_rd(partition->address, &read_data[0], &read_data[1], partition->granularity,
               OTP_CTRL_STATUS_DAI_ERROR_MASK);
    }
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

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
