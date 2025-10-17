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

bool writeblank() {
    if (!transition_state_check(TEST_UNLOCKED0, raw_unlock_token)) return false;

    initialize_otp_controller();
    grant_mcu_for_fc_writes();

    const uint32_t fuse_address = CPTRA_CORE_FMC_KEY_MANIFEST_SVN;

    // Overwriting set bits in a fuse should result in an error.
    if (!dai_wr(fuse_address, 0xFFFFFFFF, 0, 32, 0)) return false;
    if (!dai_wr(fuse_address, 0, 0, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK)) return false;

    return true;
}

void main (void) { fc_run_test(true, writeblank); }
