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

bool body (void) {
    grant_caliptra_core_for_fc_writes(); 

    if (!transition_state(TEST_UNLOCKED0, raw_unlock_token, false)) return false;
    if (!wait_dai_op_idle(0)) return false;

    initialize_otp_controller();

    // Enable `otp_operation_done` and `otp_error` interrupts.
    lsu_write_32(SOC_OTP_CTRL_INTERRUPT_ENABLE, 0x3);

    /*
     * 1: An ordinary, successful DAI operation must result in an `otp_operation_done` interrupt.
     */

    if (!dai_wr(CPTRA_SS_MANUF_DEBUG_UNLOCK_TOKEN, 0x1, 0, 32, 0)) return false;

    uint32_t alert_state = lsu_read_32(SOC_OTP_CTRL_INTERRUPT_STATE);
    if (((alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_OPERATION_DONE_LOW) & 0x1 != 0x1) ||
        ((alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_ERROR_LOW) & 0x1 != 0x0)) {
        VPRINTF(LOW, "ERROR: wrong interrupt signaled\n");
        return false;
    }
    lsu_write_32(SOC_OTP_CTRL_INTERRUPT_STATE, 0x3);

    /*
     * 2: An invalid DAI operation must result in an `otp_error` interrupt.
     */

    grant_mcu_for_fc_writes();
    if (!dai_wr(CPTRA_CORE_UDS_SEED, 0x1, 0x1, 64, OTP_CTRL_STATUS_DAI_ERROR_MASK))
        return false;

    alert_state = lsu_read_32(SOC_OTP_CTRL_INTERRUPT_STATE);
    if (((alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_OPERATION_DONE_LOW) & 0x1 != 0x1) ||
        ((alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_ERROR_LOW) & 0x1 != 0x1)) {
        VPRINTF(LOW, "ERROR: wrong interrupt signaled\n");
        return false;
    }
    lsu_write_32(SOC_OTP_CTRL_INTERRUPT_STATE, 0x3);


    /*
     * 3: Sanity check: triggering interrupts through the `INTR_TEST` register.
     */

    lsu_write_32(SOC_OTP_CTRL_INTERRUPT_TEST, 0x3);
    
    alert_state = lsu_read_32(SOC_OTP_CTRL_INTERRUPT_STATE);
    if (((alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_OPERATION_DONE_LOW) & 0x1 != 0x1) ||
        ((alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_ERROR_LOW) & 0x1 != 0x1)) {
        VPRINTF(LOW, "ERROR: wrong interrupt signaled\n");
        return false;
    }

    return true;
}

void main (void) { fc_run_test(false, body); }
