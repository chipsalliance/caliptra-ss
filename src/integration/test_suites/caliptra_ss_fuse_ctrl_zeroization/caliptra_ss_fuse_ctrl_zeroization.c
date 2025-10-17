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

/**
 * This function goes through a fuse controller zeroization sequence
 * (using the input port and the LCC scrap state). This actual broadcast
 * signal cannot be observed in software and must be verified through assertions.
 */
bool zeroize() {
    const uint32_t sentinel = 0xAB;
    const uint32_t granularity = 32;

    if (!transition_state(TEST_UNLOCKED0, raw_unlock_token, false)) return false;
    if (!wait_dai_op_idle(0)) return false;

    initialize_otp_controller();

    // 0x000: CPTRA_CORE_MANUF_DEBUG_UNLOCK_TOKEN
    grant_caliptra_core_for_fc_writes();
    if (!dai_wr(0x000, sentinel, 0, granularity, 0)) return false;

    reset_fc_lcc_rtl();
    if (!wait_dai_op_idle(0)) return false;

    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FC_FORCE_ZEROIZATION);
    if (!wait_dai_op_idle(0)) return false;

    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_RELEASE_ZEROIZATION);
    if (!wait_dai_op_idle(0)) return false;

    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FC_FORCE_ZEROIZATION_RESET);
    if (!wait_dai_op_idle(0)) return false;

    return true;
}

void main (void) { fc_run_test(true, zeroize); }
