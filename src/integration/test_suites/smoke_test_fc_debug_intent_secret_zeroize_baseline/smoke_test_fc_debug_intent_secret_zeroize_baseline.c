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
#include <stdbool.h>
#include <stdint.h>

#include "caliptra_ss_lc_ctrl_address_map.h"
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

typedef struct secret_digest_info {
    const char *name;
    uint32_t id;
    uint32_t digest0;
    uint32_t digest1;
} secret_digest_info_t;

static const secret_digest_info_t k_secret_digests[] = {
    {
        .name = "SECRET_MANUF_PARTITION",
        .id = SECRET_MANUF_PARTITION,
        .digest0 = SOC_OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_1,
    },
    {
        .name = "SECRET_PROD_PARTITION_0",
        .id = SECRET_PROD_PARTITION_0,
        .digest0 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_1,
    },
    {
        .name = "SECRET_PROD_PARTITION_1",
        .id = SECRET_PROD_PARTITION_1,
        .digest0 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_DIGEST_1,
    },
    {
        .name = "SECRET_PROD_PARTITION_2",
        .id = SECRET_PROD_PARTITION_2,
        .digest0 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_DIGEST_1,
    },
    {
        .name = "SECRET_LC_TRANSITION_PARTITION",
        .id = SECRET_LC_TRANSITION_PARTITION,
        .digest0 = SOC_OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_DIGEST_1,
    },
    {
        .name = "VENDOR_SECRET_PROD_PARTITION",
        .id = VENDOR_SECRET_PROD_PARTITION,
        .digest0 = SOC_OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_0,
        .digest1 = SOC_OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_1,
    },
};

static void check_ss_debug_intent_low(void) {
    uint32_t debug_intent = lsu_read_32(SOC_MCI_TOP_MCI_REG_SS_DEBUG_INTENT);
    if (debug_intent & MCI_REG_SS_DEBUG_INTENT_DEBUG_INTENT_MASK) {
        handle_error("ERROR: SS_DEBUG_INTENT bit0 is unexpectedly high\n");
    }
}

static void check_secret_digests_nonzero(void) {
    for (uint32_t i = 0; i < sizeof(k_secret_digests) / sizeof(k_secret_digests[0]); i++) {
        uint32_t csr_digest0 = lsu_read_32(k_secret_digests[i].digest0);
        uint32_t csr_digest1 = lsu_read_32(k_secret_digests[i].digest1);
        uint32_t dai_digest0 = 0;
        uint32_t dai_digest1 = 0;
        const partition_t partition = partitions[k_secret_digests[i].id];

        VPRINTF(LOW, "INFO: %s baseline CSR digest: 0x%08X_0x%08X\n",
                k_secret_digests[i].name, csr_digest1, csr_digest0);
        if (csr_digest0 == 0 && csr_digest1 == 0) {
            handle_error("ERROR: provisioned secret partition digest was zero in baseline\n");
        }

        grant_caliptra_core_for_fc_writes();
        if (!dai_rd(partition.digest_address, &dai_digest0, &dai_digest1, 64, 0)) {
            revoke_grant_mcu_for_fc_writes();
            handle_error("ERROR: baseline DAI digest read failed\n");
        }
        revoke_grant_mcu_for_fc_writes();
        VPRINTF(LOW, "INFO: %s baseline DAI digest: 0x%08X_0x%08X\n",
                k_secret_digests[i].name, dai_digest1, dai_digest0);
        if (dai_digest0 == 0 && dai_digest1 == 0) {
            handle_error("ERROR: provisioned secret partition DAI digest was zero in baseline\n");
        }
        if (csr_digest0 != dai_digest0 || csr_digest1 != dai_digest1) {
            handle_error("ERROR: baseline CSR and DAI digests did not match\n");
        }
    }
}

void main(void) {
    VPRINTF(LOW, "==============================================\n"
                 "MCU debug-intent secret zeroize baseline test\n"
                 "==============================================\n\n");

    mcu_cptra_init_d();
    wait_dai_op_idle(0);
    lcc_initialization();

    check_ss_debug_intent_low();
    check_secret_digests_nonzero();

    SEND_STDOUT_CTRL(0xff);
}
