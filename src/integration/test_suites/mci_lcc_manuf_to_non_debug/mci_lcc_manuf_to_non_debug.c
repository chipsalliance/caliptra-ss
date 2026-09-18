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
// Test: mci_lcc_manuf_to_non_debug
//
// Transitions the device RAW -> TEST_UNLOCKED0 -> MANUF (DEV).  From MANUF,
// xorshift32 selects two independent paths:
//
//   Translator sub-state (bit 0):
//     0 = TRANSLATOR_MANUF_NON_DEBUG  (PPD=0, debug_locked=1)
//     1 = TRANSLATOR_MANUF_DEBUG      (PPD=1, debug_locked=0)
//
//   Terminating action (bit 1):
//     0 = state_error injection  -> TRANSLATOR_NON_DEBUG
//     1 = SCRAP transition       -> SCRAP state
//
// In both cases SECURITY_STATE must show DEVICE_PRODUCTION(0x3) + debug_locked=1.
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

#define LIFECYCLE_MANUFACTURING  (0x1u)
#define LIFECYCLE_PRODUCTION     (0x3u)

// TEX (TEST_EXIT -> MANUF) token - must match test_unlock_token.hjson
static const uint32_t tex_token[4] = {
    0x2f533ae9, 0x341d2478, 0x5f066362, 0xb5fe1577
};

static const uint32_t zero_token[4] = {
    0, 0, 0, 0
};

static const uint32_t manuf_unlock[16] = {
    0x9d2fee5e, 0xd6ad3ab7, 0xde49acb6, 0x32afd8f2,
    0xc9cddd33, 0xd5ed2846, 0xc34b9649, 0xb3a54fa3,
    0x67343f15, 0x908277c6, 0xc6779c52, 0xfe55fd7d,
    0x96966232, 0xcd03999d, 0x90b3fae2, 0x7f04e213
};

static const uint32_t mbox_data[9] = {
    0xFFFFF8E2,
    0xEBEFCDAB,
    0x00000000,
    0x00000000,
    0x00000000,
    0x00000000,
    0x00000000,
    0x00000000,
    0x8A8888F8
};

volatile int rst_count = 0;
volatile int use_scrap = 0;

void main(void) {
    uint32_t sec_state;
    uint32_t lifecycle;

    if (rst_count == 1) {
        sec_state = lsu_read_32(SOC_MCI_TOP_MCI_REG_SECURITY_STATE);
        lifecycle = sec_state & MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_MASK;
        uint32_t expected = use_scrap ? LIFECYCLE_PRODUCTION : LIFECYCLE_MANUFACTURING;
        if (lifecycle != expected) {
            VPRINTF(LOW, "ERROR: expected %s(0x%x), got lifecycle=0x%x (SECURITY_STATE=0x%08x)\n",
                    use_scrap ? "LIFECYCLE_PRODUCTION" : "LIFECYCLE_MANUFACTURING", expected, lifecycle, sec_state);
            SEND_STDOUT_CTRL(0x01);
            while(1);
        }
        SEND_STDOUT_CTRL(0xff);
        while(1);
    }

    uint32_t rand_val  = xorshift32();
    uint32_t use_debug = rand_val & 1;
    use_scrap = (rand_val >> 1) & 1;

    rst_count += 1;

    VPRINTF(LOW, "=================\nMCU mci_lcc_manuf_to_non_debug\n=================\n\n");

    if (use_scrap) {
        force_PPD_pin();
    }

    lcc_initialization();
    grant_mcu_for_fc_writes();

    // RAW -> TEST_UNLOCKED0
    transition_state_check(TEST_UNLOCKED0, raw_unlock_token);
    lcc_initialization();
    grant_mcu_for_fc_writes();
    initialize_otp_controller();

    // TEST_UNLOCKED0 -> MANUF
    transition_state_check(MANUF, tex_token);
    lcc_initialization();
    wait_dai_op_idle(0);

    mcu_cptra_init_d(.cfg_skip_set_fuse_done=true);

    // Verify MANUFACTURING lifecycle and expected debug_locked
    sec_state = lsu_read_32(SOC_SOC_IFC_REG_CPTRA_SECURITY_STATE);
    lifecycle = sec_state & SOC_IFC_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_MASK;
    if (lifecycle != LIFECYCLE_MANUFACTURING) {
        VPRINTF(LOW, "ERROR: expected MANUFACTURING(0x%x) in MANUF state, got lifecycle=0x%x (SECURITY_STATE=0x%08x)\n",
                LIFECYCLE_MANUFACTURING, lifecycle, sec_state);
        SEND_STDOUT_CTRL(0x01);
        return;
    }

    if (use_debug) {
        uint32_t base_address = SOC_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0;
        uint32_t cptra_boot_go;
        lsu_write_32(SOC_SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ, SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_MANUF_DBG_UNLOCK_REQ_MASK);
        for (int i = 0; i < 16; i++) {
            VPRINTF(LOW, "MCU: writing 0x%x to address of 0x%x\n", manuf_unlock[i], base_address + (i * 4));
            lsu_write_32(base_address + (i * 4), manuf_unlock[i]);
        }
        mcu_cptra_set_fuse_done();
        mcu_cptra_advance_brkpoint();
        mcu_cptra_user_init();

        cptra_boot_go = 0;
        VPRINTF(LOW, "MCU: waits in success loop\n");
        while(cptra_boot_go != SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_MASK){
            cptra_boot_go = lsu_read_32(SOC_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP) &
                SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_MASK;
            mcu_sleep(10);
        }

        while((lsu_read_32(SOC_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK));
        VPRINTF(LOW, "MCU: Mbox lock acquired\n");
        lsu_write_32(SOC_MBOX_CSR_MBOX_CMD, 0x4D445554 | MBOX_CMD_FIELD_RESP_MASK);
        lsu_write_32(SOC_MBOX_CSR_MBOX_DLEN, 36);
        for (uint32_t ii = 0; ii < 9; ii++) {
            lsu_write_32(SOC_MBOX_CSR_MBOX_DATAIN, mbox_data[ii]);
        }
        lsu_write_32(SOC_MBOX_CSR_MBOX_EXECUTE, MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);
        VPRINTF(LOW, "MCU: Mbox execute\n");

        cptra_boot_go = 0;
        while(cptra_boot_go != SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_MASK){
            cptra_boot_go = lsu_read_32(SOC_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP) &
                SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_MASK;
            mcu_sleep(500);
        }

        while(cptra_boot_go != 0){
            cptra_boot_go = lsu_read_32(SOC_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP) &
                SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_MASK;
            mcu_sleep(500);
        }

        if (lsu_read_32(SOC_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP) &
                SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_FAIL_MASK) {
                VPRINTF(LOW, "ERROR: MANUF unlock failed\n");
                SEND_STDOUT_CTRL(0x01);
            while(1);
        }
    }

    sec_state = lsu_read_32(SOC_SOC_IFC_REG_CPTRA_SECURITY_STATE);
    lifecycle = sec_state & SOC_IFC_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_MASK;
    uint32_t exp_locked = use_debug ? 0u : 1u;
    uint32_t act_locked = !!(sec_state & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK);
    if (act_locked != exp_locked) {
        VPRINTF(LOW, "ERROR: MANUF state expected debug_locked=%u (%s), got %u (SECURITY_STATE=0x%08x)\n",
                exp_locked, use_debug ? "MANUF_DEBUG" : "MANUF_NON_DEBUG", act_locked, sec_state);
        SEND_STDOUT_CTRL(0x01);
        return;
    }
    VPRINTF(LOW, "INFO: MANUF state OK - lifecycle=MANUFACTURING(0x%x), debug_locked=%u [%s] (SECURITY_STATE=0x%08x)\n",
            lifecycle, act_locked, use_debug ? "MANUF_DEBUG" : "MANUF_NON_DEBUG", sec_state);

    if (use_scrap) {
        VPRINTF(LOW, "INFO: SCRAP path - issuing SCRAP transition from MANUF\n");
        transition_state(SCRAP, zero_token, 0);
        wait_dai_op_idle(0);
    } else {
        VPRINTF(LOW, "INFO: state_error path - injecting state_error into MCI LCC translator\n");
        lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_INJECT_STATE_ERROR);

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
    }

    // Verify DEVICE_PRODUCTION + debug_locked=1
    sec_state = lsu_read_32(SOC_MCI_TOP_MCI_REG_SECURITY_STATE);
    lifecycle = sec_state & MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_MASK;
    if (lifecycle != LIFECYCLE_PRODUCTION) {
        VPRINTF(LOW, "ERROR: expected DEVICE_PRODUCTION(0x%x), got lifecycle=0x%x (SECURITY_STATE=0x%08x)\n",
                LIFECYCLE_PRODUCTION, lifecycle, sec_state);
        SEND_STDOUT_CTRL(0x01);
        return;
    }
    if (!(sec_state & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK)) {
        VPRINTF(LOW, "ERROR: expected debug_locked=1 after %s, SECURITY_STATE=0x%08x\n",
                use_scrap ? "SCRAP\n" : "state_error\n", sec_state);
        SEND_STDOUT_CTRL(0x01);
        return;
    }
    VPRINTF(LOW, "INFO: DEVICE_PRODUCTION confirmed - lifecycle=0x%x, debug_locked=1 (SECURITY_STATE=0x%08x)\n",
            lifecycle, sec_state);

    if (!use_scrap) {
        lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LC_RELEASE_STATE_ERROR);
    }

    for (uint8_t i = 0; i < 160; i++) {
        __asm__ volatile ("nop");
    }
    SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
    while(1);
}
