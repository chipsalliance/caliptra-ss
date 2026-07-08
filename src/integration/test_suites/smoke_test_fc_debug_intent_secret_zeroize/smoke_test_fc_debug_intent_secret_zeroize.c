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
#include <stddef.h>
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

typedef struct secret_partition_info {
    const char *name;
    uint32_t id;
    uint32_t digest0;
    uint32_t digest1;
} secret_partition_info_t;

static const secret_partition_info_t k_secret_partitions[] = {
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

static void check_ss_debug_intent_high(void) {
    uint32_t debug_intent = lsu_read_32(SOC_MCI_TOP_MCI_REG_SS_DEBUG_INTENT);
    if ((debug_intent & MCI_REG_SS_DEBUG_INTENT_DEBUG_INTENT_MASK) == 0) {
        handle_error("ERROR: SS_DEBUG_INTENT bit0 is not high\n");
    }
}

static void check_secret_digests_zero(void) {
    for (uint32_t i = 0; i < sizeof(k_secret_partitions) / sizeof(k_secret_partitions[0]); i++) {
        uint32_t digest0 = lsu_read_32(k_secret_partitions[i].digest0);
        uint32_t digest1 = lsu_read_32(k_secret_partitions[i].digest1);
        VPRINTF(LOW, "INFO: %s CSR digest: 0x%08X_0x%08X\n",
                k_secret_partitions[i].name, digest1, digest0);
        if (digest0 != 0 || digest1 != 0) {
            handle_error("ERROR: secret partition digest was not zero under debug intent\n");
        }
    }

    grant_caliptra_core_for_fc_writes();
    for (uint32_t i = 0; i < sizeof(k_secret_partitions) / sizeof(k_secret_partitions[0]); i++) {
        uint32_t digest0 = 0;
        uint32_t digest1 = 0;
        const partition_t partition = partitions[k_secret_partitions[i].id];

        if (!dai_rd(partition.digest_address, &digest0, &digest1, 64, 0)) {
            handle_error("ERROR: secret partition DAI digest read failed under debug intent\n");
        }
        VPRINTF(LOW, "INFO: %s DAI digest: 0x%08X_0x%08X\n",
                k_secret_partitions[i].name, digest1, digest0);
        if (digest0 != 0 || digest1 != 0) {
            handle_error("ERROR: secret partition DAI digest was not zero under debug intent\n");
        }
    }
    revoke_grant_mcu_for_fc_writes();
}

static void check_secret_dai_access_locked(void) {
    uint32_t rdata0 = 0;
    uint32_t rdata1 = 0;
    const uint32_t granularity = partitions[SECRET_PROD_PARTITION_3].granularity;

    // SECRET_PROD_PARTITION_3 is deliberately left unprovisioned/unlocked in
    // the VMEM. Without the debug-intent strap, FIELD_ENTROPY_3 DAI writes and
    // reads would succeed, so these denials prove M1's forced read/write locks.

    grant_caliptra_core_for_fc_writes();
    if (!dai_wr(CPTRA_CORE_FIELD_ENTROPY_3, 0xdeadbeef, 0xcafebabe,
                granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK)) {
        handle_error("ERROR: unlocked FE3 DAI write did not report DAI error under debug intent\n");
    }
    reset_fc_lcc_rtl();
    if (!dai_rd(CPTRA_CORE_FIELD_ENTROPY_3, &rdata0, &rdata1,
                granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK)) {
        handle_error("ERROR: unlocked FE3 DAI read-after-write did not report DAI error under debug intent\n");
    }
    reset_fc_lcc_rtl();
    revoke_grant_mcu_for_fc_writes();
}

static void check_non_secret_dai_access_works(void) {
    uint32_t rdata0 = 0;
    uint32_t rdata1 = 0;
    const uint32_t expected = 0xa5a55a5a;

    grant_mcu_for_fc_writes();
    if (!dai_wr(VENDOR_TEST, expected, 0, partitions[VENDOR_TEST_PARTITION].granularity, 0)) {
        revoke_grant_mcu_for_fc_writes();
        handle_error("ERROR: non-secret DAI write failed\n");
    }
    if (!dai_rd(VENDOR_TEST, &rdata0, &rdata1, partitions[VENDOR_TEST_PARTITION].granularity, 0)) {
        revoke_grant_mcu_for_fc_writes();
        handle_error("ERROR: non-secret DAI read failed\n");
    }
    revoke_grant_mcu_for_fc_writes();

    if (rdata0 != expected) {
        VPRINTF(LOW, "ERROR: VENDOR_TEST readback mismatch: exp=0x%08X act=0x%08X\n",
                expected, rdata0);
        handle_error("ERROR: non-secret DAI readback mismatch\n");
    }
}

static void check_lc_functionality(void) {
    uint8_t lc_state = read_lc_state();
    uint8_t lc_counter = read_lc_counter();

    if (lc_state != MANUF) {
        VPRINTF(LOW, "ERROR: LC state mismatch: exp=%d act=%d\n", MANUF, lc_state);
        handle_error("ERROR: unexpected LC state\n");
    }
    VPRINTF(LOW, "INFO: DEV LC counter readback: %d\n", lc_counter);

    force_PPD_pin();
    if (!transition_state_check(SCRAP, NULL)) {
        handle_error("ERROR: DEV to SCRAP transition failed\n");
    }
}

void main(void) {
    VPRINTF(LOW, "=====================================\n"
                 "MCU debug-intent secret zeroize test\n"
                 "=====================================\n\n");

    mcu_cptra_init_d();
    wait_dai_op_idle(0);
    lcc_initialization();

    check_ss_debug_intent_high();
    check_secret_digests_zero();
    check_secret_dai_access_locked();
    check_non_secret_dai_access_works();
    check_lc_functionality();

    SEND_STDOUT_CTRL(0xff);
}
