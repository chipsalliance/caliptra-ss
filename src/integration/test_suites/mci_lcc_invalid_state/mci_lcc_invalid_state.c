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
//
// Test: mci_lcc_invalid_state
//
// Transitions the device RAW -> TEST_UNLOCKED0
//
// Check that device is in Unlocked state
// Force INVALID state on the otp_static_state and reset rtl
//
// Check that LCC reports TEST_UNLOCKED0, but device is locked and in production
// mode.
//
// Randomly select either SCRAP request or state_error signal to be raised.
// Release otp_static_state and check that device is still locked, and in the
// SCRAP state if that path was selected.
//
//********************************************************************************
#include <stdint.h>

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

#define DEVICE_UNPROVISIONED     (0x0u)
#define LIFECYCLE_PRODUCTION     (0x3u)

static const uint32_t zero_token[4] = {
    0, 0, 0, 0
};

void main(void) {
    uint32_t rand_val  = xorshift32();

    VPRINTF(LOW, "=================\nMCU mci_lcc_invalid_state\n=================\n\n");

    lcc_initialization();
    grant_mcu_for_fc_writes();
    transition_state_check(TEST_UNLOCKED0, raw_unlock_token);
    lcc_initialization();

    uint32_t sec_state = lsu_read_32(SOC_MCI_TOP_MCI_REG_SECURITY_STATE);
    uint32_t lifecycle = sec_state & MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_MASK;
    VPRINTF(LOW, "Checking device security state\n");
    if (lifecycle != DEVICE_UNPROVISIONED || (sec_state & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK) != 0) {
        VPRINTF(LOW, "ERROR: expected LIFECYCLE_PRODUCTION(0x%x) in TRANSLATOR_UNPROV_DEBUG state, got lifecycle=0x%x (SECURITY_STATE=0x%08x)\n",
                DEVICE_UNPROVISIONED, lifecycle, sec_state);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }

    VPRINTF(LOW, "Injecting invalid state to the lcc_st_trans otp_static_state\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_INJECT_INVALID_OTP_STATE);
    reset_fc_lcc_rtl();
    lcc_initialization();

    VPRINTF(LOW, "Checking device security state after forcing otp_static_state into invalid state\n");
    sec_state = lsu_read_32(SOC_MCI_TOP_MCI_REG_SECURITY_STATE);
    lifecycle = sec_state & MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_MASK;
    if (lifecycle != LIFECYCLE_PRODUCTION || (sec_state & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK) == 0) {
        VPRINTF(LOW, "ERROR: expected LIFECYCLE_PRODUCTION(0x%x) in TRANSLATOR_UNPROV_DEBUG state, got lifecycle=0x%x (SECURITY_STATE=0x%08x)\n",
                LIFECYCLE_PRODUCTION, lifecycle, sec_state);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }

    if (rand_val & 1) {
        lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_INJECT_STATE_ERROR);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_RELEASE_OTP_STATE);
        VPRINTF(LOW, "Checking device security state after releasing otp_static_state and forcing state_error\n");
        sec_state = lsu_read_32(SOC_MCI_TOP_MCI_REG_SECURITY_STATE);
        lifecycle = sec_state & MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_MASK;
        if (lifecycle != LIFECYCLE_PRODUCTION || (sec_state & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK) == 0) {
            VPRINTF(LOW, "ERROR: expected LIFECYCLE_PRODUCTION(0x%x) in TRANSLATOR_UNPROV_DEBUG state, got lifecycle=0x%x (SECURITY_STATE=0x%08x)\n",
                    LIFECYCLE_PRODUCTION, lifecycle, sec_state);
            SEND_STDOUT_CTRL(0x01);
            while(1);
        }
        lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_RELEASE_STATE_ERROR);
        VPRINTF(LOW, "Checking device security state after releasing otp_static_state and state_error\n");
        sec_state = lsu_read_32(SOC_MCI_TOP_MCI_REG_SECURITY_STATE);
        lifecycle = sec_state & MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_MASK;
        if (lifecycle != LIFECYCLE_PRODUCTION || (sec_state & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK) == 0) {
            VPRINTF(LOW, "ERROR: expected LIFECYCLE_PRODUCTION(0x%x) in TRANSLATOR_UNPROV_DEBUG state, got lifecycle=0x%x (SECURITY_STATE=0x%08x)\n",
                    LIFECYCLE_PRODUCTION, lifecycle, sec_state);
            SEND_STDOUT_CTRL(0x01);
            while(1);
        }
        reset_fc_lcc_rtl();
        lcc_initialization();
        sec_state = lsu_read_32(SOC_MCI_TOP_MCI_REG_SECURITY_STATE);
        lifecycle = sec_state & MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_MASK;
        if (lifecycle != DEVICE_UNPROVISIONED || (sec_state & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK) != 0) {
            VPRINTF(LOW, "ERROR: expected LIFECYCLE_PRODUCTION(0x%x) in TRANSLATOR_UNPROV_DEBUG state, got lifecycle=0x%x (SECURITY_STATE=0x%08x)\n",
                    DEVICE_UNPROVISIONED, lifecycle, sec_state);
            SEND_STDOUT_CTRL(0x01);
            while(1);
        }
    } else {
        force_PPD_pin();
        transition_state(SCRAP, zero_token, 0);
        wait_dai_op_idle(0);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_RELEASE_OTP_STATE);
        VPRINTF(LOW, "Checking device security state after releasing otp_static_state and entering SCRAP state\n");
        sec_state = lsu_read_32(SOC_MCI_TOP_MCI_REG_SECURITY_STATE);
        lifecycle = sec_state & MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_MASK;
        if (lifecycle != LIFECYCLE_PRODUCTION || (sec_state & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK) == 0) {
            VPRINTF(LOW, "ERROR: expected LIFECYCLE_PRODUCTION(0x%x) in TRANSLATOR_UNPROV_DEBUG state, got lifecycle=0x%x (SECURITY_STATE=0x%08x)\n",
                    LIFECYCLE_PRODUCTION, lifecycle, sec_state);
            SEND_STDOUT_CTRL(0x01);
            while(1);
        }
    }

    SEND_STDOUT_CTRL(0xff);
    while(1);
}
