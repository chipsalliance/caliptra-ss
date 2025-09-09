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
#include "fuse_ctrl_mmap.h"


volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// TODO ammend test description
/**
   This tests:
   1 - writes to each ratchet seed one by one and reads back the value written was returned.
   2 - Write, then read the digest for all HEKs
   3 - tries writing and reading and checking a DAI error is returned
   4 - zeroize all the HEK fuses and markers
 */

void zeroization_marker_write_read(void) {
    uint32_t r_data[2];
    uint32_t w_data[2] = {0x03, 0x03};
    partition_t partition = partitions[VENDOR_SECRET_PROD_PARTITION];

    /* dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_0].zer_address, w_data[0], w_data[1], 64, 0 /\*OTP_CTRL_STATUS_DAI_ERROR_MASK*\/); */
    /* VPRINTF(LOW, "=====================================================\n"); */
    /* VPRINTF(LOW, "Attempted to write zeroization marker for HEK0 : results in error\n"); */
    /* VPRINTF(LOW, "=====================================================\n"); */
    /* dai_rd(partitions[CPTRA_SS_LOCK_HEK_PROD_0].zer_address, &r_data[0], &r_data[1], 64, 0); */


    dai_wr(partition.zer_address, w_data[0], w_data[1], 64, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    VPRINTF(LOW, "=====================================================\n");
    VPRINTF(LOW, "Attempted to write zeroization marker for HEK0 : results in e**or\n");
    VPRINTF(LOW, "=====================================================\n");
    dai_rd(partition.zer_address, &r_data[0], &r_data[1], 64, 0);

    VPRINTF(LOW, "r_data[0]=%0d, &r_data[1]=%0d", r_data[0], &r_data[1]);

    VPRINTF(LOW, "=====================================================\n");
    VPRINTF(LOW, "Read zeroization marker for HEK0 : no e**or\n");
    VPRINTF(LOW, "=====================================================\n");

epilogue:
    VPRINTF(LOW, "zeroization_marker_write_read test finished\n");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    initialize_otp_controller();

    VPRINTF(LOW, "=================\nBefore ratchet_seed_write_read\n=================\n\n")
    zeroization_marker_write_read();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
