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
// Test: mci_lcc_state_error_to_locked
//
// Transitions the device to TEST_UNLOCKED0 and verifies that the security state
// shows DEVICE_UNPROVISIONED with debug_locked=0.  Then injects state_error into
// the MCI LCC state translator.  The FSM transitions to TRANSLATOR_NON_DEBUG,
// which drives device_lifecycle=DEVICE_PRODUCTION(0x3) and debug_locked=1.
// After releasing the injection the FSM remains in TRANSLATOR_NON_DEBUG
// (self-locking - reset is required to escape), so both fields must still read
// DEVICE_PRODUCTION + debug_locked=1.
//
// SECURITY_STATE register layout:
//   bits [1:0]  device_lifecycle  (0x0=UNPROVISIONED, 0x1=MANUFACTURING, 0x3=PRODUCTION)
//   bit  [2]    debug_locked
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

// device_lifecycle field encoding (bits [1:0] of SECURITY_STATE)
#define LIFECYCLE_UNPROVISIONED  (0x0u)
#define LIFECYCLE_PRODUCTION     (0x3u)

void main(void) {
    VPRINTF(LOW, "=================\nMCU mci_lcc_state_error_to_locked\n=================\n\n");

    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    lcc_initialization();
    grant_mcu_for_fc_writes();

    transition_state_check(TEST_UNLOCKED0, raw_unlock_token);

    initialize_otp_controller();

    // Verify initial state: DEVICE_UNPROVISIONED, debug_locked=0.
    uint32_t sec_state = lsu_read_32(SOC_MCI_TOP_MCI_REG_SECURITY_STATE);
    uint32_t lifecycle  = sec_state & MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_MASK;
    if (sec_state & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK) {
        VPRINTF(LOW, "ERROR: expected debug_locked=0 before injection, got SECURITY_STATE=0x%08x\n", sec_state);
        SEND_STDOUT_CTRL(0x01);
        return;
    }
    if (lifecycle != LIFECYCLE_UNPROVISIONED) {
        VPRINTF(LOW, "ERROR: expected DEVICE_UNPROVISIONED(0x%x) before injection, got lifecycle=0x%x (SECURITY_STATE=0x%08x)\n",
                LIFECYCLE_UNPROVISIONED, lifecycle, sec_state);
        SEND_STDOUT_CTRL(0x01);
        return;
    }
    VPRINTF(LOW, "INFO: initial state OK - lifecycle=0x%x, debug_locked=0 (SECURITY_STATE=0x%08x)\n", lifecycle, sec_state);

    // Inject state_error.
    VPRINTF(LOW, "INFO: injecting state_error into MCI LCC state translator\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_INJECT_STATE_ERROR);

    // Poll until debug_locked==1.
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

    // Verify device_lifecycle is DEVICE_PRODUCTION.
    lifecycle = sec_state & MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_MASK;
    if (lifecycle != LIFECYCLE_PRODUCTION) {
        VPRINTF(LOW, "ERROR: expected DEVICE_PRODUCTION(0x%x) after injection, got lifecycle=0x%x (SECURITY_STATE=0x%08x)\n",
                LIFECYCLE_PRODUCTION, lifecycle, sec_state);
        SEND_STDOUT_CTRL(0x01);
        return;
    }
    VPRINTF(LOW, "INFO: locked state OK - lifecycle=DEVICE_PRODUCTION(0x%x), debug_locked=1 (SECURITY_STATE=0x%08x)\n",
            lifecycle, sec_state);

    // Release the injected state_error.
    VPRINTF(LOW, "INFO: releasing state_error injection\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_RELEASE_STATE_ERROR);

    // Allow a few cycles to settle.
    for (uint8_t i = 0; i < 32; i++) {
        __asm__ volatile ("nop");
    }

    // Verify the FSM remains in TRANSLATOR_NON_DEBUG after release:
    // DEVICE_PRODUCTION + debug_locked=1 must persist without a reset.
    sec_state = lsu_read_32(SOC_MCI_TOP_MCI_REG_SECURITY_STATE);
    lifecycle  = sec_state & MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_MASK;
    if (!(sec_state & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK)) {
        VPRINTF(LOW, "ERROR: debug_locked unexpectedly cleared after state_error release (SECURITY_STATE=0x%08x)\n", sec_state);
        SEND_STDOUT_CTRL(0x01);
        return;
    }
    if (lifecycle != LIFECYCLE_PRODUCTION) {
        VPRINTF(LOW, "ERROR: device_lifecycle changed after state_error release - expected 0x%x, got 0x%x (SECURITY_STATE=0x%08x)\n",
                LIFECYCLE_PRODUCTION, lifecycle, sec_state);
        SEND_STDOUT_CTRL(0x01);
        return;
    }
    VPRINTF(LOW, "INFO: post-release state OK - lifecycle=DEVICE_PRODUCTION(0x%x), debug_locked=1 (SECURITY_STATE=0x%08x)\n",
            lifecycle, sec_state);

    for (uint8_t i = 0; i < 160; i++) {
        __asm__ volatile ("nop");
    }

    SEND_STDOUT_CTRL(0xff);
}
