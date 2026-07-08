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
#include <stdint.h>

#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "fuse_ctrl_mmap.h"
#include "lc_ctrl.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"
#include "soc_ifc.h"

volatile char *stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

typedef struct secret_program_target {
    const char *name;
    uint32_t id;
    uint32_t fuse_addr;
    uint32_t digest0;
    uint32_t digest1;
} secret_program_target_t;

static const secret_program_target_t k_secret_program_targets[] = {
    {
        .name = "SECRET_MANUF_PARTITION",
        .id = SECRET_MANUF_PARTITION,
        .fuse_addr = CPTRA_CORE_UDS_SEED,
        .digest0 = SOC_OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_1,
    },
    {
        .name = "SECRET_PROD_PARTITION_0",
        .id = SECRET_PROD_PARTITION_0,
        .fuse_addr = CPTRA_CORE_FIELD_ENTROPY_0,
        .digest0 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_1,
    },
    {
        .name = "SECRET_PROD_PARTITION_1",
        .id = SECRET_PROD_PARTITION_1,
        .fuse_addr = CPTRA_CORE_FIELD_ENTROPY_1,
        .digest0 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_DIGEST_1,
    },
    {
        .name = "SECRET_PROD_PARTITION_2",
        .id = SECRET_PROD_PARTITION_2,
        .fuse_addr = CPTRA_CORE_FIELD_ENTROPY_2,
        .digest0 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_DIGEST_1,
    },
    {
        .name = "SECRET_PROD_PARTITION_3",
        .id = SECRET_PROD_PARTITION_3,
        .fuse_addr = CPTRA_CORE_FIELD_ENTROPY_3,
        .digest0 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_DIGEST_1,
    },
    {
        .name = "SECRET_LC_TRANSITION_PARTITION",
        .id = SECRET_LC_TRANSITION_PARTITION,
        .fuse_addr = CPTRA_SS_TEST_UNLOCK_TOKEN_1,
        .digest0 = SOC_OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_DIGEST_1,
    },
    {
        .name = "VENDOR_SECRET_PROD_PARTITION",
        .id = VENDOR_SECRET_PROD_PARTITION,
        .fuse_addr = CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_0,
        .digest0 = SOC_OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_1,
    },
};

static void check_ss_debug_intent_high(void) {
    uint32_t debug_intent = lsu_read_32(SOC_MCI_TOP_MCI_REG_SS_DEBUG_INTENT);
    if ((debug_intent & MCI_REG_SS_DEBUG_INTENT_DEBUG_INTENT_MASK) == 0) {
        handle_error("ERROR: SS_DEBUG_INTENT bit0 is not high\n");
    }
}

static void check_secret_digest_still_blank(const secret_program_target_t *target) {
    uint32_t digest0 = lsu_read_32(target->digest0);
    uint32_t digest1 = lsu_read_32(target->digest1);

    VPRINTF(LOW, "INFO: %s digest after denied program: 0x%08X_0x%08X\n",
            target->name, digest1, digest0);
    if (digest0 != 0 || digest1 != 0) {
        handle_error("ERROR: secret digest changed after denied programming attempt\n");
    }
}

static void attempt_secret_programming_under_debug_intent(void) {
    const uint32_t data0 = 0xa5a5a5a5;
    const uint32_t data1 = 0x5a5a5a5a;

    grant_caliptra_core_for_fc_writes();
    for (uint32_t i = 0; i < sizeof(k_secret_program_targets) / sizeof(k_secret_program_targets[0]); i++) {
        const secret_program_target_t *target = &k_secret_program_targets[i];
        VPRINTF(LOW, "INFO: Attempting DAI program of unlocked %s under debug intent\n",
                target->name);
        if (!dai_wr(target->fuse_addr, data0, data1,
                    partitions[target->id].granularity,
                    OTP_CTRL_STATUS_DAI_ERROR_MASK)) {
            revoke_grant_mcu_for_fc_writes();
            handle_error("ERROR: secret DAI write was not denied under debug intent\n");
        }
        check_secret_digest_still_blank(target);
    }
    revoke_grant_mcu_for_fc_writes();
}

void main(void) {
    VPRINTF(LOW, "=================================================\n"
                 "MCU debug-intent secret program-blocked test\n"
                 "=================================================\n\n");

    mcu_cptra_init_d();
    wait_dai_op_idle(0);
    lcc_initialization();

    check_ss_debug_intent_high();
    attempt_secret_programming_under_debug_intent();

    SEND_STDOUT_CTRL(0xff);
}
