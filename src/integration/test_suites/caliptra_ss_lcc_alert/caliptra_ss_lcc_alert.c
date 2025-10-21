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


bool body (void) {
    // Fault a bit in an AXI write request, which will transfer the LCC into a terminal state.
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LCC_FATAL_BUS_INTEG_ERROR);
    lsu_write_32(SOC_LC_CTRL_ALERT_TEST, 0x1);

    mcu_sleep(160);

    uint32_t lcc_status = lsu_read_32(SOC_LC_CTRL_STATUS);

    if (! ((lcc_status >> LC_CTRL_STATUS_BUS_INTEG_ERROR_LOW) & 1)) {
        VPRINTF(LOW, "ERROR: bus integ error not signaled in status register\n");
        return false;
    }

    return true;
}

void main (void) { fc_run_test(false, body); }
