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

#include "fuse_ctrl_mmap.h"

const partition_t partitions[NUM_PARTITIONS] = {
    // SW_TEST_UNLOCK_PARTITION
    {
        .index = 0,
        .address = 0x0000,
        .digest_address = 0x0040,
        .zer_address = 0x0000,
        .variant = 0,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = true,
        .sw_digest = false,
        .has_ecc = true,
        .lc_phase = 16,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = sw_test_unlock_partition_fuses
    },
    // SECRET_MANUF_PARTITION
    {
        .index = 1,
        .address = 0x0048,
        .digest_address = 0x0088,
        .zer_address = 0x0090,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_ecc = true,
        .lc_phase = 16,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = secret_manuf_partition_fuses
    },
    // SECRET_PROD_PARTITION_0
    {
        .index = 2,
        .address = 0x0098,
        .digest_address = 0x00A0,
        .zer_address = 0x00A8,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = secret_prod_partition_0_fuses
    },
    // SECRET_PROD_PARTITION_1
    {
        .index = 3,
        .address = 0x00B0,
        .digest_address = 0x00B8,
        .zer_address = 0x00C0,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = secret_prod_partition_1_fuses
    },
    // SECRET_PROD_PARTITION_2
    {
        .index = 4,
        .address = 0x00C8,
        .digest_address = 0x00D0,
        .zer_address = 0x00D8,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = secret_prod_partition_2_fuses
    },
    // SECRET_PROD_PARTITION_3
    {
        .index = 5,
        .address = 0x00E0,
        .digest_address = 0x00E8,
        .zer_address = 0x00F0,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = secret_prod_partition_3_fuses
    },
    // SW_MANUF_PARTITION
    {
        .index = 6,
        .address = 0x00F8,
        .digest_address = 0x02F8,
        .zer_address = 0x0000,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_ecc = true,
        .lc_phase = 16,
        .is_lifecycle = false,
        .num_fuses = 13,
        .fuses = sw_manuf_partition_fuses
    },
    // SECRET_LC_TRANSITION_PARTITION
    {
        .index = 7,
        .address = 0x0300,
        .digest_address = 0x03B0,
        .zer_address = 0x0000,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_ecc = true,
        .lc_phase = 1,
        .is_lifecycle = false,
        .num_fuses = 11,
        .fuses = secret_lc_transition_partition_fuses
    },
    // SVN_PARTITION
    {
        .index = 8,
        .address = 0x03B8,
        .digest_address = 0x0000,
        .zer_address = 0x0000,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = false,
        .has_ecc = false,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 4,
        .fuses = svn_partition_fuses
    },
    // VENDOR_TEST_PARTITION
    {
        .index = 9,
        .address = 0x03E0,
        .digest_address = 0x0418,
        .zer_address = 0x0000,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_ecc = false,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = vendor_test_partition_fuses
    },
    // VENDOR_HASHES_MANUF_PARTITION
    {
        .index = 10,
        .address = 0x0420,
        .digest_address = 0x0458,
        .zer_address = 0x0000,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_ecc = false,
        .lc_phase = 16,
        .is_lifecycle = false,
        .num_fuses = 2,
        .fuses = vendor_hashes_manuf_partition_fuses
    },
    // VENDOR_HASHES_PROD_PARTITION
    {
        .index = 11,
        .address = 0x0460,
        .digest_address = 0x07B8,
        .zer_address = 0x0000,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_ecc = false,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 34,
        .fuses = vendor_hashes_prod_partition_fuses
    },
    // VENDOR_REVOCATIONS_PROD_PARTITION
    {
        .index = 12,
        .address = 0x07C0,
        .digest_address = 0x0890,
        .zer_address = 0x0000,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_ecc = false,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 51,
        .fuses = vendor_revocations_prod_partition_fuses
    },
    // VENDOR_SECRET_PROD_PARTITION
    {
        .index = 13,
        .address = 0x0898,
        .digest_address = 0x0A98,
        .zer_address = 0x0AA0,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 16,
        .fuses = vendor_secret_prod_partition_fuses
    },
    // VENDOR_NON_SECRET_PROD_PARTITION
    {
        .index = 14,
        .address = 0x0AA8,
        .digest_address = 0x0CA8,
        .zer_address = 0x0000,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 16,
        .fuses = vendor_non_secret_prod_partition_fuses
    },
    // CPTRA_SS_LOCK_HEK_PROD_0
    {
        .index = 15,
        .address = 0x0CB0,
        .digest_address = 0x0CD0,
        .zer_address = 0x0CD8,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = cptra_ss_lock_hek_prod_0_fuses
    },
    // CPTRA_SS_LOCK_HEK_PROD_1
    {
        .index = 16,
        .address = 0x0CE0,
        .digest_address = 0x0D00,
        .zer_address = 0x0D08,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = cptra_ss_lock_hek_prod_1_fuses
    },
    // CPTRA_SS_LOCK_HEK_PROD_2
    {
        .index = 17,
        .address = 0x0D10,
        .digest_address = 0x0D30,
        .zer_address = 0x0D38,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = cptra_ss_lock_hek_prod_2_fuses
    },
    // CPTRA_SS_LOCK_HEK_PROD_3
    {
        .index = 18,
        .address = 0x0D40,
        .digest_address = 0x0D60,
        .zer_address = 0x0D68,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = cptra_ss_lock_hek_prod_3_fuses
    },
    // CPTRA_SS_LOCK_HEK_PROD_4
    {
        .index = 19,
        .address = 0x0D70,
        .digest_address = 0x0D90,
        .zer_address = 0x0D98,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = cptra_ss_lock_hek_prod_4_fuses
    },
    // CPTRA_SS_LOCK_HEK_PROD_5
    {
        .index = 20,
        .address = 0x0DA0,
        .digest_address = 0x0DC0,
        .zer_address = 0x0DC8,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = cptra_ss_lock_hek_prod_5_fuses
    },
    // CPTRA_SS_LOCK_HEK_PROD_6
    {
        .index = 21,
        .address = 0x0DD0,
        .digest_address = 0x0DF0,
        .zer_address = 0x0DF8,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = cptra_ss_lock_hek_prod_6_fuses
    },
    // CPTRA_SS_LOCK_HEK_PROD_7
    {
        .index = 22,
        .address = 0x0E00,
        .digest_address = 0x0E20,
        .zer_address = 0x0E28,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = cptra_ss_lock_hek_prod_7_fuses
    },
    // LIFE_CYCLE
    {
        .index = 23,
        .address = 0x0E30,
        .digest_address = 0x0000,
        .zer_address = 0x0000,
        .variant = 2,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = false,
        .has_ecc = true,
        .lc_phase = 0,
        .is_lifecycle = true,
        .num_fuses = 2,
        .fuses = life_cycle_fuses
    },
};

const uint32_t sw_test_unlock_partition_fuses[] = {
    CPTRA_SS_MANUF_DEBUG_UNLOCK_TOKEN
};
const uint32_t secret_manuf_partition_fuses[] = {
    CPTRA_CORE_UDS_SEED
};
const uint32_t secret_prod_partition_0_fuses[] = {
    CPTRA_CORE_FIELD_ENTROPY_0
};
const uint32_t secret_prod_partition_1_fuses[] = {
    CPTRA_CORE_FIELD_ENTROPY_1
};
const uint32_t secret_prod_partition_2_fuses[] = {
    CPTRA_CORE_FIELD_ENTROPY_2
};
const uint32_t secret_prod_partition_3_fuses[] = {
    CPTRA_CORE_FIELD_ENTROPY_3
};
const uint32_t sw_manuf_partition_fuses[] = {
    CPTRA_CORE_ANTI_ROLLBACK_DISABLE,
    CPTRA_CORE_IDEVID_CERT_IDEVID_ATTR,
    SOC_SPECIFIC_IDEVID_CERTIFICATE,
    CPTRA_CORE_IDEVID_MANUF_HSM_IDENTIFIER,
    CPTRA_CORE_SOC_STEPPING_ID,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_0,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_1,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_2,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_3,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_4,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_5,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_6,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_7
};
const uint32_t secret_lc_transition_partition_fuses[] = {
    CPTRA_SS_TEST_UNLOCK_TOKEN_1,
    CPTRA_SS_TEST_UNLOCK_TOKEN_2,
    CPTRA_SS_TEST_UNLOCK_TOKEN_3,
    CPTRA_SS_TEST_UNLOCK_TOKEN_4,
    CPTRA_SS_TEST_UNLOCK_TOKEN_5,
    CPTRA_SS_TEST_UNLOCK_TOKEN_6,
    CPTRA_SS_TEST_UNLOCK_TOKEN_7,
    CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN,
    CPTRA_SS_MANUF_TO_PROD_TOKEN,
    CPTRA_SS_PROD_TO_PROD_END_TOKEN,
    CPTRA_SS_RMA_TOKEN
};
const uint32_t svn_partition_fuses[] = {
    CPTRA_CORE_FMC_KEY_MANIFEST_SVN,
    CPTRA_CORE_RUNTIME_SVN,
    CPTRA_CORE_SOC_MANIFEST_SVN,
    CPTRA_CORE_SOC_MANIFEST_MAX_SVN
};
const uint32_t vendor_test_partition_fuses[] = {
    VENDOR_TEST
};
const uint32_t vendor_hashes_manuf_partition_fuses[] = {
    CPTRA_CORE_VENDOR_PK_HASH_0,
    CPTRA_CORE_PQC_KEY_TYPE_0
};
const uint32_t vendor_hashes_prod_partition_fuses[] = {
    CPTRA_SS_OWNER_PK_HASH,
    CPTRA_SS_OWNER_PQC_KEY_TYPE,
    CPTRA_SS_OWNER_PK_HASH_VALID,
    CPTRA_CORE_VENDOR_PK_HASH_1,
    CPTRA_CORE_PQC_KEY_TYPE_1,
    CPTRA_CORE_VENDOR_PK_HASH_2,
    CPTRA_CORE_PQC_KEY_TYPE_2,
    CPTRA_CORE_VENDOR_PK_HASH_3,
    CPTRA_CORE_PQC_KEY_TYPE_3,
    CPTRA_CORE_VENDOR_PK_HASH_4,
    CPTRA_CORE_PQC_KEY_TYPE_4,
    CPTRA_CORE_VENDOR_PK_HASH_5,
    CPTRA_CORE_PQC_KEY_TYPE_5,
    CPTRA_CORE_VENDOR_PK_HASH_6,
    CPTRA_CORE_PQC_KEY_TYPE_6,
    CPTRA_CORE_VENDOR_PK_HASH_7,
    CPTRA_CORE_PQC_KEY_TYPE_7,
    CPTRA_CORE_VENDOR_PK_HASH_8,
    CPTRA_CORE_PQC_KEY_TYPE_8,
    CPTRA_CORE_VENDOR_PK_HASH_9,
    CPTRA_CORE_PQC_KEY_TYPE_9,
    CPTRA_CORE_VENDOR_PK_HASH_10,
    CPTRA_CORE_PQC_KEY_TYPE_10,
    CPTRA_CORE_VENDOR_PK_HASH_11,
    CPTRA_CORE_PQC_KEY_TYPE_11,
    CPTRA_CORE_VENDOR_PK_HASH_12,
    CPTRA_CORE_PQC_KEY_TYPE_12,
    CPTRA_CORE_VENDOR_PK_HASH_13,
    CPTRA_CORE_PQC_KEY_TYPE_13,
    CPTRA_CORE_VENDOR_PK_HASH_14,
    CPTRA_CORE_PQC_KEY_TYPE_14,
    CPTRA_CORE_VENDOR_PK_HASH_15,
    CPTRA_CORE_PQC_KEY_TYPE_15,
    CPTRA_CORE_VENDOR_PK_HASH_VALID
};
const uint32_t vendor_revocations_prod_partition_fuses[] = {
    CPTRA_SS_OWNER_ECC_REVOCATION,
    CPTRA_SS_OWNER_LMS_REVOCATION,
    CPTRA_SS_OWNER_MLDSA_REVOCATION,
    CPTRA_CORE_ECC_REVOCATION_0,
    CPTRA_CORE_LMS_REVOCATION_0,
    CPTRA_CORE_MLDSA_REVOCATION_0,
    CPTRA_CORE_ECC_REVOCATION_1,
    CPTRA_CORE_LMS_REVOCATION_1,
    CPTRA_CORE_MLDSA_REVOCATION_1,
    CPTRA_CORE_ECC_REVOCATION_2,
    CPTRA_CORE_LMS_REVOCATION_2,
    CPTRA_CORE_MLDSA_REVOCATION_2,
    CPTRA_CORE_ECC_REVOCATION_3,
    CPTRA_CORE_LMS_REVOCATION_3,
    CPTRA_CORE_MLDSA_REVOCATION_3,
    CPTRA_CORE_ECC_REVOCATION_4,
    CPTRA_CORE_LMS_REVOCATION_4,
    CPTRA_CORE_MLDSA_REVOCATION_4,
    CPTRA_CORE_ECC_REVOCATION_5,
    CPTRA_CORE_LMS_REVOCATION_5,
    CPTRA_CORE_MLDSA_REVOCATION_5,
    CPTRA_CORE_ECC_REVOCATION_6,
    CPTRA_CORE_LMS_REVOCATION_6,
    CPTRA_CORE_MLDSA_REVOCATION_6,
    CPTRA_CORE_ECC_REVOCATION_7,
    CPTRA_CORE_LMS_REVOCATION_7,
    CPTRA_CORE_MLDSA_REVOCATION_7,
    CPTRA_CORE_ECC_REVOCATION_8,
    CPTRA_CORE_LMS_REVOCATION_8,
    CPTRA_CORE_MLDSA_REVOCATION_8,
    CPTRA_CORE_ECC_REVOCATION_9,
    CPTRA_CORE_LMS_REVOCATION_9,
    CPTRA_CORE_MLDSA_REVOCATION_9,
    CPTRA_CORE_ECC_REVOCATION_10,
    CPTRA_CORE_LMS_REVOCATION_10,
    CPTRA_CORE_MLDSA_REVOCATION_10,
    CPTRA_CORE_ECC_REVOCATION_11,
    CPTRA_CORE_LMS_REVOCATION_11,
    CPTRA_CORE_MLDSA_REVOCATION_11,
    CPTRA_CORE_ECC_REVOCATION_12,
    CPTRA_CORE_LMS_REVOCATION_12,
    CPTRA_CORE_MLDSA_REVOCATION_12,
    CPTRA_CORE_ECC_REVOCATION_13,
    CPTRA_CORE_LMS_REVOCATION_13,
    CPTRA_CORE_MLDSA_REVOCATION_13,
    CPTRA_CORE_ECC_REVOCATION_14,
    CPTRA_CORE_LMS_REVOCATION_14,
    CPTRA_CORE_MLDSA_REVOCATION_14,
    CPTRA_CORE_ECC_REVOCATION_15,
    CPTRA_CORE_LMS_REVOCATION_15,
    CPTRA_CORE_MLDSA_REVOCATION_15
};
const uint32_t vendor_secret_prod_partition_fuses[] = {
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_0,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_1,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_2,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_3,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_4,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_5,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_6,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_7,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_8,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_9,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_10,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_11,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_12,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_13,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_14,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_15
};
const uint32_t vendor_non_secret_prod_partition_fuses[] = {
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_0,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_1,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_2,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_3,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_4,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_5,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_6,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_7,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_8,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_9,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_10,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_11,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_12,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_13,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_14,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_15
};
const uint32_t cptra_ss_lock_hek_prod_0_fuses[] = {
    CPTRA_SS_LOCK_HEK_PROD_0_RATCHET_SEED
};
const uint32_t cptra_ss_lock_hek_prod_1_fuses[] = {
    CPTRA_SS_LOCK_HEK_PROD_1_RATCHET_SEED
};
const uint32_t cptra_ss_lock_hek_prod_2_fuses[] = {
    CPTRA_SS_LOCK_HEK_PROD_2_RATCHET_SEED
};
const uint32_t cptra_ss_lock_hek_prod_3_fuses[] = {
    CPTRA_SS_LOCK_HEK_PROD_3_RATCHET_SEED
};
const uint32_t cptra_ss_lock_hek_prod_4_fuses[] = {
    CPTRA_SS_LOCK_HEK_PROD_4_RATCHET_SEED
};
const uint32_t cptra_ss_lock_hek_prod_5_fuses[] = {
    CPTRA_SS_LOCK_HEK_PROD_5_RATCHET_SEED
};
const uint32_t cptra_ss_lock_hek_prod_6_fuses[] = {
    CPTRA_SS_LOCK_HEK_PROD_6_RATCHET_SEED
};
const uint32_t cptra_ss_lock_hek_prod_7_fuses[] = {
    CPTRA_SS_LOCK_HEK_PROD_7_RATCHET_SEED
};
const uint32_t life_cycle_fuses[] = {
    LC_TRANSITION_CNT,
    LC_STATE
};
