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

#ifndef FUSE_CTRL_MMAP_HEADER
#define FUSE_CTRL_MMAP_HEADER

typedef enum {
    // SW_TEST_UNLOCK_PARTITION
    CPTRA_CORE_MANUF_DEBUG_UNLOCK_TOKEN = 0x0000,
    // SECRET_MANUF_PARTITION
    CPTRA_CORE_UDS_SEED = 0x0048,
    // SECRET_PROD_PARTITION_0
    CPTRA_CORE_FIELD_ENTROPY_0 = 0x0090,
    // SECRET_PROD_PARTITION_1
    CPTRA_CORE_FIELD_ENTROPY_1 = 0x00A0,
    // SECRET_PROD_PARTITION_2
    CPTRA_CORE_FIELD_ENTROPY_2 = 0x00B0,
    // SECRET_PROD_PARTITION_3
    CPTRA_CORE_FIELD_ENTROPY_3 = 0x00C0,
    // SW_MANUF_PARTITION
    CPTRA_CORE_ANTI_ROLLBACK_DISABLE = 0x00D0,
    CPTRA_CORE_IDEVID_CERT_IDEVID_ATTR = 0x00D1,
    CPTRA_CORE_IDEVID_MANUF_HSM_IDENTIFIER = 0x1FE1,
    CPTRA_CORE_SOC_STEPPING_ID = 0x1FF1,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_0 = 0x1FF3,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_1 = 0x2023,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_2 = 0x2053,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_3 = 0x2083,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_4 = 0x20B3,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_5 = 0x20E3,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_6 = 0x2113,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_7 = 0x2143,
    // SECRET_LC_TRANSITION_PARTITION
    CPTRA_SS_TEST_UNLOCK_TOKEN_1 = 0x2C18,
    CPTRA_SS_TEST_UNLOCK_TOKEN_2 = 0x2C28,
    CPTRA_SS_TEST_UNLOCK_TOKEN_3 = 0x2C38,
    CPTRA_SS_TEST_UNLOCK_TOKEN_4 = 0x2C48,
    CPTRA_SS_TEST_UNLOCK_TOKEN_5 = 0x2C58,
    CPTRA_SS_TEST_UNLOCK_TOKEN_6 = 0x2C68,
    CPTRA_SS_TEST_UNLOCK_TOKEN_7 = 0x2C78,
    CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN = 0x2C88,
    CPTRA_SS_MANUF_TO_PROD_TOKEN = 0x2C98,
    CPTRA_SS_PROD_TO_PROD_END_TOKEN = 0x2CA8,
    CPTRA_SS_RMA_TOKEN = 0x2CB8,
    // SVN_PARTITION
    CPTRA_CORE_FMC_KEY_MANIFEST_SVN = 0x2CD0,
    CPTRA_CORE_RUNTIME_SVN = 0x2CD4,
    CPTRA_CORE_SOC_MANIFEST_SVN = 0x2CE4,
    CPTRA_CORE_SOC_MANIFEST_MAX_SVN = 0x2CF4,
    // VENDOR_TEST_PARTITION
    VENDOR_TEST = 0x2CF8,
    // VENDOR_HASHES_MANUF_PARTITION
    CPTRA_CORE_VENDOR_PK_HASH_0 = 0x2D38,
    CPTRA_CORE_PQC_KEY_TYPE_0 = 0x2D68,
    // VENDOR_HASHES_PROD_PARTITION
    CPTRA_CORE_VENDOR_PK_HASH_1 = 0x2D78,
    CPTRA_CORE_PQC_KEY_TYPE_1 = 0x2DA8,
    CPTRA_CORE_VENDOR_PK_HASH_2 = 0x2DA9,
    CPTRA_CORE_PQC_KEY_TYPE_2 = 0x2DD9,
    CPTRA_CORE_VENDOR_PK_HASH_3 = 0x2DDA,
    CPTRA_CORE_PQC_KEY_TYPE_3 = 0x2E0A,
    CPTRA_CORE_VENDOR_PK_HASH_4 = 0x2E0B,
    CPTRA_CORE_PQC_KEY_TYPE_4 = 0x2E3B,
    CPTRA_CORE_VENDOR_PK_HASH_5 = 0x2E3C,
    CPTRA_CORE_PQC_KEY_TYPE_5 = 0x2E6C,
    CPTRA_CORE_VENDOR_PK_HASH_6 = 0x2E6D,
    CPTRA_CORE_PQC_KEY_TYPE_6 = 0x2E9D,
    CPTRA_CORE_VENDOR_PK_HASH_7 = 0x2E9E,
    CPTRA_CORE_PQC_KEY_TYPE_7 = 0x2ECE,
    CPTRA_CORE_VENDOR_PK_HASH_8 = 0x2ECF,
    CPTRA_CORE_PQC_KEY_TYPE_8 = 0x2EFF,
    CPTRA_CORE_VENDOR_PK_HASH_9 = 0x2F00,
    CPTRA_CORE_PQC_KEY_TYPE_9 = 0x2F30,
    CPTRA_CORE_VENDOR_PK_HASH_10 = 0x2F31,
    CPTRA_CORE_PQC_KEY_TYPE_10 = 0x2F61,
    CPTRA_CORE_VENDOR_PK_HASH_11 = 0x2F62,
    CPTRA_CORE_PQC_KEY_TYPE_11 = 0x2F92,
    CPTRA_CORE_VENDOR_PK_HASH_12 = 0x2F93,
    CPTRA_CORE_PQC_KEY_TYPE_12 = 0x2FC3,
    CPTRA_CORE_VENDOR_PK_HASH_13 = 0x2FC4,
    CPTRA_CORE_PQC_KEY_TYPE_13 = 0x2FF4,
    CPTRA_CORE_VENDOR_PK_HASH_14 = 0x2FF5,
    CPTRA_CORE_PQC_KEY_TYPE_14 = 0x3025,
    CPTRA_CORE_VENDOR_PK_HASH_15 = 0x3026,
    CPTRA_CORE_PQC_KEY_TYPE_15 = 0x3056,
    CPTRA_CORE_VENDOR_PK_HASH_VALID = 0x3057,
    // VENDOR_REVOCATIONS_PROD_PARTITION
    CPTRA_CORE_ECC_REVOCATION_0 = 0x3068,
    CPTRA_CORE_LMS_REVOCATION_0 = 0x3069,
    CPTRA_CORE_MLDSA_REVOCATION_0 = 0x306D,
    CPTRA_CORE_ECC_REVOCATION_1 = 0x3071,
    CPTRA_CORE_LMS_REVOCATION_1 = 0x3072,
    CPTRA_CORE_MLDSA_REVOCATION_1 = 0x3076,
    CPTRA_CORE_ECC_REVOCATION_2 = 0x307A,
    CPTRA_CORE_LMS_REVOCATION_2 = 0x307B,
    CPTRA_CORE_MLDSA_REVOCATION_2 = 0x307F,
    CPTRA_CORE_ECC_REVOCATION_3 = 0x3083,
    CPTRA_CORE_LMS_REVOCATION_3 = 0x3084,
    CPTRA_CORE_MLDSA_REVOCATION_3 = 0x3088,
    CPTRA_CORE_ECC_REVOCATION_4 = 0x308C,
    CPTRA_CORE_LMS_REVOCATION_4 = 0x308D,
    CPTRA_CORE_MLDSA_REVOCATION_4 = 0x3091,
    CPTRA_CORE_ECC_REVOCATION_5 = 0x3095,
    CPTRA_CORE_LMS_REVOCATION_5 = 0x3096,
    CPTRA_CORE_MLDSA_REVOCATION_5 = 0x309A,
    CPTRA_CORE_ECC_REVOCATION_6 = 0x309E,
    CPTRA_CORE_LMS_REVOCATION_6 = 0x309F,
    CPTRA_CORE_MLDSA_REVOCATION_6 = 0x30A3,
    CPTRA_CORE_ECC_REVOCATION_7 = 0x30A7,
    CPTRA_CORE_LMS_REVOCATION_7 = 0x30A8,
    CPTRA_CORE_MLDSA_REVOCATION_7 = 0x30AC,
    CPTRA_CORE_ECC_REVOCATION_8 = 0x30B0,
    CPTRA_CORE_LMS_REVOCATION_8 = 0x30B1,
    CPTRA_CORE_MLDSA_REVOCATION_8 = 0x30B5,
    CPTRA_CORE_ECC_REVOCATION_9 = 0x30B9,
    CPTRA_CORE_LMS_REVOCATION_9 = 0x30BA,
    CPTRA_CORE_MLDSA_REVOCATION_9 = 0x30BE,
    CPTRA_CORE_ECC_REVOCATION_10 = 0x30C2,
    CPTRA_CORE_LMS_REVOCATION_10 = 0x30C3,
    CPTRA_CORE_MLDSA_REVOCATION_10 = 0x30C7,
    CPTRA_CORE_ECC_REVOCATION_11 = 0x30CB,
    CPTRA_CORE_LMS_REVOCATION_11 = 0x30CC,
    CPTRA_CORE_MLDSA_REVOCATION_11 = 0x30D0,
    CPTRA_CORE_ECC_REVOCATION_12 = 0x30D4,
    CPTRA_CORE_LMS_REVOCATION_12 = 0x30D5,
    CPTRA_CORE_MLDSA_REVOCATION_12 = 0x30D9,
    CPTRA_CORE_ECC_REVOCATION_13 = 0x30DD,
    CPTRA_CORE_LMS_REVOCATION_13 = 0x30DE,
    CPTRA_CORE_MLDSA_REVOCATION_13 = 0x30E2,
    CPTRA_CORE_ECC_REVOCATION_14 = 0x30E6,
    CPTRA_CORE_LMS_REVOCATION_14 = 0x30E7,
    CPTRA_CORE_MLDSA_REVOCATION_14 = 0x30EB,
    CPTRA_CORE_ECC_REVOCATION_15 = 0x30EF,
    CPTRA_CORE_LMS_REVOCATION_15 = 0x30F0,
    CPTRA_CORE_MLDSA_REVOCATION_15 = 0x30F4,
    // VENDOR_SECRET_PROD_PARTITION
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_0 = 0x3100,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_1 = 0x3120,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_2 = 0x3140,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_3 = 0x3160,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_4 = 0x3180,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_5 = 0x31A0,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_6 = 0x31C0,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_7 = 0x31E0,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_8 = 0x3200,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_9 = 0x3220,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_10 = 0x3240,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_11 = 0x3260,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_12 = 0x3280,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_13 = 0x32A0,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_14 = 0x32C0,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_15 = 0x32E0,
    // VENDOR_NON_SECRET_PROD_PARTITION
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_0 = 0x3308,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_1 = 0x3328,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_2 = 0x3348,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_3 = 0x3368,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_4 = 0x3388,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_5 = 0x33A8,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_6 = 0x33C8,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_7 = 0x33E8,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_8 = 0x3408,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_9 = 0x3428,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_10 = 0x3448,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_11 = 0x3468,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_12 = 0x3488,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_13 = 0x34A8,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_14 = 0x34C8,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_15 = 0x34E8,
    // LIFE_CYCLE
    LC_TRANSITION_CNT = 0x3FA8,
    LC_STATE = 0x3FD8
} fuse_t;

typedef struct {
    uint32_t address;
    uint32_t digest_address;
    bool is_secret;
    bool hw_digest;
    bool sw_digest;
    bool is_lifecycle;
    uint32_t num_fuses;
    uint32_t *fuses;
} partition_t;

#define NUM_PARTITIONS 16

uint32_t sw_test_unlock_partition_fuses[] = {
    CPTRA_CORE_MANUF_DEBUG_UNLOCK_TOKEN
};
uint32_t secret_manuf_partition_fuses[] = {
    CPTRA_CORE_UDS_SEED
};
uint32_t secret_prod_partition_0_fuses[] = {
    CPTRA_CORE_FIELD_ENTROPY_0
};
uint32_t secret_prod_partition_1_fuses[] = {
    CPTRA_CORE_FIELD_ENTROPY_1
};
uint32_t secret_prod_partition_2_fuses[] = {
    CPTRA_CORE_FIELD_ENTROPY_2
};
uint32_t secret_prod_partition_3_fuses[] = {
    CPTRA_CORE_FIELD_ENTROPY_3
};
uint32_t sw_manuf_partition_fuses[] = {
    CPTRA_CORE_ANTI_ROLLBACK_DISABLE,
    CPTRA_CORE_IDEVID_CERT_IDEVID_ATTR,
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
uint32_t secret_lc_transition_partition_fuses[] = {
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
uint32_t svn_partition_fuses[] = {
    CPTRA_CORE_FMC_KEY_MANIFEST_SVN,
    CPTRA_CORE_RUNTIME_SVN,
    CPTRA_CORE_SOC_MANIFEST_SVN,
    CPTRA_CORE_SOC_MANIFEST_MAX_SVN
};
uint32_t vendor_test_partition_fuses[] = {
    VENDOR_TEST
};
uint32_t vendor_hashes_manuf_partition_fuses[] = {
    CPTRA_CORE_VENDOR_PK_HASH_0,
    CPTRA_CORE_PQC_KEY_TYPE_0
};
uint32_t vendor_hashes_prod_partition_fuses[] = {
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
uint32_t vendor_revocations_prod_partition_fuses[] = {
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
uint32_t vendor_secret_prod_partition_fuses[] = {
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
uint32_t vendor_non_secret_prod_partition_fuses[] = {
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
uint32_t life_cycle_fuses[] = {
    LC_TRANSITION_CNT,
    LC_STATE
};

partition_t partitions[NUM_PARTITIONS] = {
    // SW_TEST_UNLOCK_PARTITION
    {
        .address = 0x0000,
        .digest_address = 0x0040,
        .is_secret = false,
        .hw_digest = true,
        .sw_digest = false,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = sw_test_unlock_partition_fuses
    },
    // SECRET_MANUF_PARTITION
    {
        .address = 0x0048,
        .digest_address = 0x0088,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = secret_manuf_partition_fuses
    },
    // SECRET_PROD_PARTITION_0
    {
        .address = 0x0090,
        .digest_address = 0x0098,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = secret_prod_partition_0_fuses
    },
    // SECRET_PROD_PARTITION_1
    {
        .address = 0x00A0,
        .digest_address = 0x00A8,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = secret_prod_partition_1_fuses
    },
    // SECRET_PROD_PARTITION_2
    {
        .address = 0x00B0,
        .digest_address = 0x00B8,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = secret_prod_partition_2_fuses
    },
    // SECRET_PROD_PARTITION_3
    {
        .address = 0x00C0,
        .digest_address = 0x00C8,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = secret_prod_partition_3_fuses
    },
    // SW_MANUF_PARTITION
    {
        .address = 0x00D0,
        .digest_address = 0x2C10,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .is_lifecycle = false,
        .num_fuses = 12,
        .fuses = sw_manuf_partition_fuses
    },
    // SECRET_LC_TRANSITION_PARTITION
    {
        .address = 0x2C18,
        .digest_address = 0x2CC8,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .is_lifecycle = false,
        .num_fuses = 11,
        .fuses = secret_lc_transition_partition_fuses
    },
    // SVN_PARTITION
    {
        .address = 0x2CD0,
        .digest_address = 0x0000,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = false,
        .is_lifecycle = false,
        .num_fuses = 3,
        .fuses = svn_partition_fuses
    },
    // VENDOR_TEST_PARTITION
    {
        .address = 0x2CF8,
        .digest_address = 0x2D30,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = vendor_test_partition_fuses
    },
    // VENDOR_HASHES_MANUF_PARTITION
    {
        .address = 0x2D38,
        .digest_address = 0x2D70,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .is_lifecycle = false,
        .num_fuses = 2,
        .fuses = vendor_hashes_manuf_partition_fuses
    },
    // VENDOR_HASHES_PROD_PARTITION
    {
        .address = 0x2D78,
        .digest_address = 0x3060,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .is_lifecycle = false,
        .num_fuses = 31,
        .fuses = vendor_hashes_prod_partition_fuses
    },
    // VENDOR_REVOCATIONS_PROD_PARTITION
    {
        .address = 0x3068,
        .digest_address = 0x30F8,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .is_lifecycle = false,
        .num_fuses = 48,
        .fuses = vendor_revocations_prod_partition_fuses
    },
    // VENDOR_SECRET_PROD_PARTITION
    {
        .address = 0x3100,
        .digest_address = 0x3300,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .is_lifecycle = false,
        .num_fuses = 16,
        .fuses = vendor_secret_prod_partition_fuses
    },
    // VENDOR_NON_SECRET_PROD_PARTITION
    {
        .address = 0x3308,
        .digest_address = 0x3FA0,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .is_lifecycle = false,
        .num_fuses = 16,
        .fuses = vendor_non_secret_prod_partition_fuses
    },
    // LIFE_CYCLE
    {
        .address = 0x3FA8,
        .digest_address = 0x0000,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = false,
        .is_lifecycle = true,
        .num_fuses = 2,
        .fuses = life_cycle_fuses
    }
};

#endif // FUSE_CTRL_MMAP_HEADER