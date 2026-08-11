// SPDX-License-Identifier: Apache-2.0
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
//
// ## LCC Escalation Test
// 
// This test initializes randomly the FC VMEM file and sets a random LC starting
// state as well as LC counter. Then, randomly either raise the esc_scrap_state0
// or esc_scrap_state1 port. Check, if we are in the ESCALATE LC state. Then
// try a state transition to starting state + 1. This should fail and we still
// should be in the ESCALATE LC state.
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

const uint32_t tokens[21][4] = {
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {0x72f04808, 0x05f493b4, 0x7790628a, 0x318372c8}, // CPTRA_SS_TEST_UNLOCK_TOKEN_1
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {0x17c78a78, 0xc7b443ef, 0xd6931045, 0x55e74f3c}, // CPTRA_SS_TEST_UNLOCK_TOKEN_2
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {0x1644aa12, 0x79925802, 0xdbc26815, 0x8597a5fa}, // CPTRA_SS_TEST_UNLOCK_TOKEN_3
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {0x34d1ea6e, 0x121f023f, 0x6e9dc51c, 0xc7439b6f}, // CPTRA_SS_TEST_UNLOCK_TOKEN_4
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {0x03fd9df1, 0x20978af4, 0x49db216d, 0xb0225ece}, // CPTRA_SS_TEST_UNLOCK_TOKEN_5
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {0xcfc0871c, 0xc400e922, 0x4290a4ad, 0x7f10dc89}, // CPTRA_SS_TEST_UNLOCK_TOKEN_6
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {0x67e87f3e, 0xae6ee167, 0x802efa05, 0xbaaa3138}, // CPTRA_SS_TEST_UNLOCK_TOKEN_7
    {0x2f533ae9, 0x341d2478, 0x5f066362, 0xb5fe1577}, // CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN
    {0xf622abb6, 0x5d8318f4, 0xc721179d, 0x51c001f2}, // CPTRA_SS_MANUF_TO_PROD_TOKEN
    {0x25b8649d, 0xe7818e5b, 0x826d5ba4, 0xd6b633a0}, // CPTRA_SS_PROD_TO_PROD_END_TOKEN
    {0x72f04808, 0x05f493b4, 0x7790628a, 0x318372c8}, // CPTRA_SS_RMA_TOKEN
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}  // empty
};

void trigger_escalation() {
    // Randomly raise the esc_scrap_state0 or esc_scrap_state1 escalation port.
    uint32_t rnd = xorshift32() & 1;
    if (rnd) {
        lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_TRIGGER_ESCALATION0);
    } else {
        lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_TRIGGER_ESCALATION1);
    }
}

void deassert_escalation() {
    // Randomly raise the esc_scrap_state0 or esc_scrap_state1 escalation port.
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_TRIGGER_ESCALATION0_DIS);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_TRIGGER_ESCALATION1_DIS);
}

// Local DAI-idle poll that does NOT check MCI AGG_ERROR_FATAL. This test
// deliberately drives the fuse controller into a fatal alert (fatal_check_error)
// via the escalation ports; that alert latches into the sticky (W1C)
// AGG_ERROR_FATAL and survives the FC/LCC reset, so the shared wait_dai_op_idle()
// would flag the expected escalation error. Here we only need to confirm the DAI
// is idle after the reset before reading back the LC state.
static void wait_dai_op_idle_no_fatal_check(void) {
    uint32_t status;
    // All status bits below DAI_IDLE are error bits (DAI_IDLE is the lowest of
    // the non-error status bits), so DAI_IDLE - 1 masks the error bits.
    uint32_t error_mask = OTP_CTRL_STATUS_DAI_IDLE_MASK - 1;

    for (;;) {
        status = lsu_read_32(SOC_OTP_CTRL_STATUS);

        // Has an error been reported?
        if (status & error_mask) break;

        // Has the DAI become idle, with no check pending?
        if ((status & OTP_CTRL_STATUS_DAI_IDLE_MASK) &&
            !(status & OTP_CTRL_STATUS_CHECK_PENDING_MASK)) break;
    }

    VPRINTF(LOW, "wait_dai_op_idle_no_fatal_check: 0x%08X\n", status);
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");
    
    // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring Caliptra out of reset 
    // This is just to see CSSBootFSM running correctly
    lsu_write_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, 1);
    VPRINTF(LOW, "MCU: Writing MCI SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO\n");

    uint32_t cptra_boot_go = lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO);
    VPRINTF(LOW, "MCU: Reading SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO %x\n", cptra_boot_go);

    uint32_t lc_state_curr = read_lc_state();
    uint32_t lc_state_init = lc_state_curr;

    // Check if we can increment from the current state to the next.
    // PROD_END (18) to RMA (19) not possible.
    // SCRAP (20) is the last state.
    if (lc_state_curr == 18 || lc_state_curr == 20) {
        VPRINTF(LOW, "Info: Cannot increment state from current %d state. Exit test\n", lc_state_curr);
        SEND_STDOUT_CTRL(0xff);
    }

    lcc_initialization();
    lc_state_curr = read_lc_state();
    uint32_t lc_state_next = state_sequence[lc_state_curr + 1];
    uint32_t lc_cnt_curr = read_lc_counter();
    uint32_t lc_cnt_next = lc_cnt_curr + 1;

    VPRINTF(LOW, "Triggering escalation at randomized starting state %d\n", lc_state_curr);
    trigger_escalation();

    // Wait a bit before reading out the LC state register.
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    lc_state_curr = read_lc_state();

    // Check if we are in the ESCALATE state.
    if (lc_state_curr != 22) {
        VPRINTF(LOW, "ERROR: incorrect state: exp: %d, act: %d\n", 22, lc_state_curr);
        exit(1);
    }


    VPRINTF(LOW, "Try to reach next state %d\n", lc_state_next);
    if (lc_state_next == 20) {
        // Transition to SCRAP require setting the PPD pin.
        force_PPD_pin();
    }

    const uint32_t *token = (lc_state_curr == 0) ? raw_unlock_token : tokens[lc_state_next];

    transition_state(lc_state_next, token, true);

    // Wait a bit before reading out the LC state register.
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    lc_state_curr = read_lc_state();

    deassert_escalation();

    // Check if we are still in the ESCALATE state.
    if (lc_state_curr != 22) {
        VPRINTF(LOW, "ERROR: incorrect state: exp: %d, act: %d\n", 22, lc_state_curr);
        exit(1);
    }

    // After a reset the escalation should be cleared and the lc state back at the
    // pre-reset value.
    reset_fc_lcc_rtl();
    // Use the local idle poll (not wait_dai_op_idle): the escalation deliberately
    // raised an FC fatal alert that stays latched in AGG_ERROR_FATAL, which the
    // shared helper would report as an unexpected error.
    wait_dai_op_idle_no_fatal_check();
    lc_state_curr = read_lc_state();
    if (lc_state_curr != lc_state_init) {
        VPRINTF(LOW, "ERROR: lc state has not reverted back to pre-reset value\n");
    }

    SEND_STDOUT_CTRL(0xff);
}
