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

static void nop_sleep(unsigned count) {
    for (unsigned ii = 0; ii < count; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
}

bool body(void) {
    if (!transition_state(TEST_UNLOCKED0, raw_unlock_token)) return false;

    if (!wait_dai_op_idle(0)) return false;

    initialize_otp_controller();

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
    bool is_correctable = (fault == CMD_FC_LCC_CORRECTABLE_FAULT);

    if (is_caliptra_secret_addr(partition.address)) {
        grant_caliptra_core_for_fc_writes();
    } else {
        grant_mcu_for_fc_writes();
    }

    // Write one word in the selected partition and lock it afterwards.
    if (!dai_wr(partition.address, 0x1, 0x2, partition.granularity, 0)) return false;
    calculate_digest(partition.address, 0);

    // Inject either a correctable or uncorrectable error into all locked partitions with digests
    // (as recorded in a list in fc_lcc_tb_services). In particular, this will include the selected
    // partition.
    const char *err_desc = is_correctable ? "a correctable" : "an uncorrectable";
    VPRINTF(LOW, "INFO: About to inject %s fault into partition %d.\n", err_desc, partition.index);

    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, fault);
    if (!wait_dai_op_idle(0)) return false;

    // Reset lc_ctrl. If there's a partition error, we expect it to percolate up to the status
    // register very quickly but that error will take some time to "upgrade" if this is an
    // uncorrectable error. Give the block another 1e3 cycles (which, from experiment, should be a
    // generous upper bound).
    reset_fc_lcc_rtl();
    nop_sleep(1000);

    // At this point, we want to predict the value of OTP_CTRL_STATUS that we expect. This is a bit
    // tricky, because several of the partition bits depend on lots that we don't really want to
    // model here. BUT:
    //
    //    1. We always expect the error bit for the targeted partition (1 << partition.index) to be
    //       set.
    //
    //    2. For an uncorrectable error, we expect all partition error bits set, together with
    //       DAI_ERROR and LCI_ERROR.
    //
    //    3. For a correctable error, it's a bit tricky to predict which other partitions' error
    //       bits will be set. But we *do* know that DAI_ERROR and LCI_ERROR are expected to be
    //       false.

    uint32_t the_part_error = (1 << partition.index);
    uint32_t all_part_errors = (1 << NUM_PARTITIONS) - 1;
    uint32_t top_error_bits = (OTP_CTRL_STATUS_DAI_ERROR_MASK |
                               OTP_CTRL_STATUS_LCI_ERROR_MASK);

    uint32_t error_req = 0, error_opt = 0;
    if (is_correctable) {
        error_req = the_part_error;
        error_opt = all_part_errors;
    } else {
        error_req = all_part_errors | top_error_bits;
    }

    // We could use the wait_dai_op_idle function to wait until the DAI is idle or an error happens,
    // but we expect an error to have appeared by now (and, if it is uncorrectable, the DAI will
    // never become idle).
    //
    // Instead of doing that, read the status register directly, then mask out the IDLE bit in case
    // it was set.
    uint32_t otp_status = lsu_read_32(SOC_OTP_CTRL_STATUS) & ~OTP_CTRL_STATUS_DAI_IDLE_MASK;
    bool success = true;

    if (error_req & ~otp_status) {
        VPRINTF(LOW,
                "ERROR: After %s error, not enough error bits are set. "
                "required 0x%08x; status = 0x%08x => missing: 0x%08x.\n",
                err_desc, error_req, otp_status, error_req & ~otp_status);
        success = false;
    }
    if (otp_status & ~(error_req | error_opt)) {
        VPRINTF(LOW,
                "ERROR: After %s error, extra error bits are set. "
                "status = 0x%08x; allowed = 0x%08x => extra: 0x%08x.\n",
                err_desc, otp_status, error_req | error_opt, otp_status & ~(error_req | error_opt));
        success = false;
    }

    // Predict the error code. It should be 2 (MacroEccCorrError) on a correctable error but an
    // uncorrectable error will actually cause an FSM fault, which causes all three bits of the
    // error code to go high (giving 7).
    unsigned exp_err_code = is_correctable ? 2 : 7;
    uint32_t err_code = lsu_read_32(SOC_OTP_CTRL_ERR_CODE_RF_ERR_CODE_0 + 0x4*partition.index);

    if (err_code != exp_err_code) {
        VPRINTF(LOW, "ERROR: After %s error, the error code register has %d but we expect %d.\n",
                err_desc, err_code, exp_err_code);
        success = false;
    }

    return success;
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    bool test_passed = body();

    nop_sleep(160);

    SEND_STDOUT_CTRL(test_passed ? TB_CMD_TEST_PASS : TB_CMD_TEST_FAIL);
}
