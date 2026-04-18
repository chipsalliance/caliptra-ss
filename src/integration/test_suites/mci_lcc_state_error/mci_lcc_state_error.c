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
// Test: mci_lcc_state_error
//
// Verify that asserting state_error to the MCI LCC state translator while in
// an unlocked state causes the security state to transition to debug_locked.
// After releasing the error and resetting the LCC/FC/MCI, the state should
// return to debug_unlocked (TEST_UNLOCKED0 is still in OTP).
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

void main(void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    lcc_initialization();
    grant_mcu_for_fc_writes();

    transition_state_check(TEST_UNLOCKED0, raw_unlock_token);

    initialize_otp_controller();
    wait_dai_op_idle(0);

    // Verify that the device starts with debug unlocked in TEST_UNLOCKED0.
    uint32_t sec_state = lsu_read_32(SOC_MCI_TOP_MCI_REG_SECURITY_STATE);
    if (sec_state & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK) {
        VPRINTF(LOW, "ERROR: expected debug_locked=0 before state_error injection, got SECURITY_STATE=0x%08x\n", sec_state);
        SEND_STDOUT_CTRL(0x01);
        return;
    }
    VPRINTF(LOW, "INFO: debug_locked=0 confirmed before state_error injection (SECURITY_STATE=0x%08x)\n", sec_state);

    // Force state_error high via the testbench service.
    VPRINTF(LOW, "INFO: injecting state_error into MCI LCC state translator\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_INJECT_STATE_ERROR);

    // Poll until debug_locked == 1.
    uint32_t locked = 0;
    for (uint32_t i = 0; i < 10000; i++) {
        sec_state = lsu_read_32(SOC_MCI_TOP_MCI_REG_SECURITY_STATE);
        if (sec_state & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK) {
            locked = 1;
            break;
        }
    }
    if (!locked) {
        VPRINTF(LOW, "ERROR: debug_locked did not become 1 after state_error injection (SECURITY_STATE=0x%08x)\n", sec_state);
        SEND_STDOUT_CTRL(0x01);
        return;
    }
    VPRINTF(LOW, "INFO: debug_locked=1 confirmed after state_error injection (SECURITY_STATE=0x%08x)\n", sec_state);

    // Release the injected state_error.
    VPRINTF(LOW, "INFO: releasing state_error injection\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_RELEASE_STATE_ERROR);

    // Reset FC/LCC/MCI to recover the unlocked state.
    // After reset the translator will re-evaluate OTP state (still TEST_UNLOCKED0)
    // and return to TRANSLATOR_UNPROV_DEBUG with debug_locked=0.
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);
    lcc_initialization();

    // Poll until debug_locked == 0.
    uint32_t unlocked = 0;
    for (uint32_t i = 0; i < 10000; i++) {
        sec_state = lsu_read_32(SOC_MCI_TOP_MCI_REG_SECURITY_STATE);
        if (!(sec_state & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK)) {
            unlocked = 1;
            break;
        }
    }
    if (!unlocked) {
        VPRINTF(LOW, "ERROR: debug_locked did not return to 0 after reset (SECURITY_STATE=0x%08x)\n", sec_state);
        SEND_STDOUT_CTRL(0x01);
        return;
    }
    VPRINTF(LOW, "INFO: debug_locked=0 confirmed after reset (SECURITY_STATE=0x%08x)\n", sec_state);

    for (uint8_t i = 0; i < 160; i++) {
        __asm__ volatile ("nop");
    }

    SEND_STDOUT_CTRL(0xff);
}
