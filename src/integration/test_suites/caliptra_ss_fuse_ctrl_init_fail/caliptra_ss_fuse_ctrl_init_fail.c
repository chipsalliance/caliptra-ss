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

void init_fail() {
    const uint32_t faults[2] = {
        CMD_FC_LCC_CORRECTABLE_FAULT,
        CMD_FC_LCC_UNCORRECTABLE_FAULT
    };

    // Collect all buffered partitions with ECC enabled. Their content
    // will be read out after bringup which will trigger the ECC errors.
    partition_t part_sel[NUM_PARTITIONS];

    uint32_t count = 0;
    for (int i = 0; i < NUM_PARTITIONS; i++) {
        if (partitions[i].variant == 0 && partitions[i].has_ecc) {
            part_sel[count++] = partitions[i];
        }
    } 

    partition_t partition = part_sel[xorshift32() % count];
    uint32_t fault = faults[xorshift32() % 2];

    if (is_caliptra_secret_addr(partition.address)) {
        grant_caliptra_core_for_fc_writes();
    } else {
        grant_mcu_for_fc_writes();
    }

    // Write one word in the selected partition and lock it afterwards.
    dai_wr(partition.address, 0x1, 0x2, partition.granularity, 0);
    calculate_digest(partition.address, 0);

    // Inject either a correctable or uncorrectable error into all locked partitions with digests
    // (as recorded in a list in fc_lcc_tb_services). In particular, this will include the selected
    // partition.
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, fault);
    wait_dai_op_idle(0);

    reset_fc_lcc_rtl();

    // If the fault was correctable, we expect the DAI to stop with an error on the bit
    // corresponding to the partition (which will be 1 << partition.index). If it was uncorrectable,
    // we expect the DAI to stop with all partition error bits set, together with DAI_ERROR and
    // LCI_ERROR.
    uint32_t single_error = 1 << partition.index;
    uint32_t all_part_errors = (1 << NUM_PARTITIONS) - 1;
    uint32_t uncor_error = (all_part_errors |
                            OTP_CTRL_STATUS_DAI_ERROR_MASK |
                            OTP_CTRL_STATUS_LCI_ERROR_MASK);

    uint32_t exp_dai_error = (fault == CMD_FC_LCC_CORRECTABLE_FAULT) ? single_error : uncor_error;

    if (!wait_dai_op_idle(exp_dai_error)) return;

    const char *err_desc = ((fault == CMD_FC_LCC_CORRECTABLE_FAULT) ?
                            "a correctable" : "an uncorrectable");
    unsigned exp_err_code = (fault == CMD_FC_LCC_CORRECTABLE_FAULT) ? 2 : 3;
    uint32_t err_code = lsu_read_32(SOC_OTP_CTRL_ERR_CODE_RF_ERR_CODE_0 + 0x4*partition.index);

    if (err_code != exp_err_code)
        VPRINTF(LOW, "ERROR: After %s error, the error code register has %d but we expect %d.\n",
                err_desc, err_code, exp_err_code);
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    transition_state(TEST_UNLOCKED0, raw_unlock_token);
    wait_dai_op_idle(0);

    initialize_otp_controller();

    init_fail();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
