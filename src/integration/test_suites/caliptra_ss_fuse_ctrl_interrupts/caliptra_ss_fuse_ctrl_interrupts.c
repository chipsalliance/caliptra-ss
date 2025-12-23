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

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    uint32_t alert_state, operation_done, otp_error;
      
    initialize_otp_controller();

    // Enable `otp_operation_done` and `otp_error` interrupts.
    lsu_write_32(SOC_OTP_CTRL_INTERRUPT_ENABLE, 0x3);


    /*
     * 1: Sanity check: triggering interrupts through the `INTR_TEST` register.
     */

    lsu_write_32(SOC_OTP_CTRL_INTERRUPT_TEST, 0x3);
    
    alert_state = lsu_read_32(SOC_OTP_CTRL_INTERRUPT_STATE);

    operation_done = (alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_OPERATION_DONE_LOW) & 0x1;
    otp_error = (alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_ERROR_LOW) & 0x1;

    if (operation_done != 0x1 || otp_error != 0x1) {
        handle_error("ERROR: INTERRUPT_TEST register does not work as expected.\n");
    }

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);
    // Enable `otp_operation_done` and `otp_error` interrupts.
    lsu_write_32(SOC_OTP_CTRL_INTERRUPT_ENABLE, 0x3);
    alert_state = lsu_read_32(SOC_OTP_CTRL_INTERRUPT_STATE); // Read back to ensure clear
    if (alert_state != 0x0) {
        handle_error("ERROR: interrupt state register was not cleared properly.\n");
    }

    /*
     * 2: An ordinary, successful DAI operation must result in an `otp_operation_done` interrupt.
     */

    dai_wr(CPTRA_SS_MANUF_DEBUG_UNLOCK_TOKEN, 0x1, 0, 32, 0);

    alert_state = lsu_read_32(SOC_OTP_CTRL_INTERRUPT_STATE);

    operation_done = (alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_OPERATION_DONE_LOW) & 0x1;
    otp_error = (alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_ERROR_LOW) & 0x1;

    if (operation_done != 0x1 || otp_error != 0x0) {
        handle_error("ERROR: wrong interrupt signaled\n");
    }


    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);
    // Enable `otp_operation_done` and `otp_error` interrupts.
    lsu_write_32(SOC_OTP_CTRL_INTERRUPT_ENABLE, 0x3);
    alert_state = lsu_read_32(SOC_OTP_CTRL_INTERRUPT_STATE); // Read back to ensure clear
    if (alert_state != 0x0) {
        handle_error("ERROR: interrupt state register was not cleared properly.\n");
    }

    /*
     * 3: An invalid DAI operation must result in an `otp_error` interrupt.
     */


    dai_wr(CPTRA_CORE_UDS_SEED, 0x1, 0x1, 64, OTP_CTRL_STATUS_DAI_ERROR_MASK); // invalid AXI ID

    alert_state = lsu_read_32(SOC_OTP_CTRL_INTERRUPT_STATE);
    operation_done = (alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_OPERATION_DONE_LOW) & 0x1;
    otp_error = (alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_ERROR_LOW) & 0x1;

    if (operation_done != 0x1 || otp_error != 0x1) {
        handle_error("ERROR: error indication signal was not asserted.\n");
    }

    VPRINTF(LOW, "INFO: All interrupt tests passed successfully.\n");
    SEND_STDOUT_CTRL(0xff);
}
