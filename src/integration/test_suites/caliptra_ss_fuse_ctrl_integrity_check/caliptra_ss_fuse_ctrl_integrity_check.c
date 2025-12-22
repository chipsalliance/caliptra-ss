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

void fuse_ctrl_short_integrity_check_init(void) {
    uint32_t status;

    // Step 1: Check OTP controller initialization status
    VPRINTF(LOW, "DEBUG: Checking OTP controller initialization status...\n");
    status = lsu_read_32(SOC_OTP_CTRL_STATUS);

    // Check for error bits in the status register
    if (status & 0x3FFFFF != 0 ) { // Mask all bits except DAI_IDLE
        VPRINTF(LOW, "ERROR: OTP controller initialization failed. STATUS: 0x%08X\n", status);
        return;
    }

    wait_dai_op_idle(0);

    VPRINTF(LOW, "INFO: OTP controller successfully initialized. STATUS: 0x%08X\n", status);

    // Step 2: Set up periodic background checks
    VPRINTF(LOW, "DEBUG: Configuring periodic background checks...\n");
    
    // Configure CHECK_TIMEOUT
    uint32_t check_timeout = 0x100000; // Example value, adjust as needed
    lsu_write_32(SOC_OTP_CTRL_CHECK_TIMEOUT, check_timeout);
    VPRINTF(LOW, "INFO: CHECK_TIMEOUT set to 0x%08X\n", check_timeout);

    // Configure INTEGRITY_CHECK_PERIOD
    uint32_t integrity_check_period = 0xFFF; // Example value, adjust as needed
    lsu_write_32(SOC_OTP_CTRL_INTEGRITY_CHECK_PERIOD, integrity_check_period);
    VPRINTF(LOW, "INFO: INTEGRITY_CHECK_PERIOD set to 0x%08X\n", integrity_check_period);

    // Configure CONSISTENCY_CHECK_PERIOD
    uint32_t consistency_check_period = 0xFFF; // Example value, adjust as needed
    lsu_write_32(SOC_OTP_CTRL_CONSISTENCY_CHECK_PERIOD, consistency_check_period);
    VPRINTF(LOW, "INFO: CONSISTENCY_CHECK_PERIOD set to 0x%08X\n", consistency_check_period);

    // Step 3: Lock down background check registers
    VPRINTF(LOW, "DEBUG: Locking background check registers...\n");
    lsu_write_32(SOC_OTP_CTRL_CHECK_REGWEN, 0x0);
    VPRINTF(LOW, "INFO: CHECK_REGWEN locked.\n");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    /*
     * The transition tokens partitions is initialized with random data
     * but a valid digest. The initial integrity check should then pass.
     * Afterwards, the digest is manually altered which then should transfer
     * the fuse controller into a terminal state after triggering a new
     * integrity check by setting the period and timeout registers.
     */

    VPRINTF(LOW, "1/4: Initialising\n");
    mcu_cptra_init_d();
    fuse_ctrl_short_integrity_check_init();

    VPRINTF(LOW, "2/4: Injecting digest fault\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FC_LCC_FAULT_DIGEST);

    VPRINTF(LOW, "3/4: Initialising OTP controller\n");
    

    // After injecting an error into a digest, we expect all the partitions to report an error which
    // will also cause several other errors to be reported. We do not, however, expect a bus
    // integrity error or a timeout error.
    //
    // The bus integrity error doesn't take partition integrity into account, so won't be generated.
    // The timeout error error is caused by a partition not responding in time. Again, that isn't
    // caused by injecting a fault in a partition so won't be reported here.
    uint32_t exp_error = ~(OTP_CTRL_STATUS_BUS_INTEG_ERROR_MASK |
                           OTP_CTRL_STATUS_TIMEOUT_ERROR_MASK);

    mcu_sleep(1000); // Wait for some time before triggering the integrity check.

    VPRINTF(LOW, "4/4: Checking for DAI status\n");
    wait_dai_op_idle(exp_error);

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
