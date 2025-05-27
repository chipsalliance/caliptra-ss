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
#define FUSE_CTRL_MMAP_HEADERS

typedef enum {
    // SW_TEST_UNLOCK_PARTITION
    CPTRA_SS_MANUF_DEBUG_UNLOCK_TOKEN = 0x0000,
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
    SOC_SPECIFIC_IDEVID_CERTIFICATE = 0x0131,
    CPTRA_CORE_IDEVID_MANUF_HSM_IDENTIFIER = 0x0135,
    CPTRA_CORE_SOC_STEPPING_ID = 0x0145,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_0 = 0x0147,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_1 = 0x0177,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_2 = 0x01A7,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_3 = 0x01D7,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_4 = 0x0207,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_5 = 0x0237,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_6 = 0x0267,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_7 = 0x0297,
    // SECRET_LC_TRANSITION_PARTITION
    CPTRA_SS_TEST_UNLOCK_TOKEN_1 = 0x04A0,
    CPTRA_SS_TEST_UNLOCK_TOKEN_2 = 0x04B0,
    CPTRA_SS_TEST_UNLOCK_TOKEN_3 = 0x04C0,
    CPTRA_SS_TEST_UNLOCK_TOKEN_4 = 0x04D0,
    CPTRA_SS_TEST_UNLOCK_TOKEN_5 = 0x04E0,
    CPTRA_SS_TEST_UNLOCK_TOKEN_6 = 0x04F0,
    CPTRA_SS_TEST_UNLOCK_TOKEN_7 = 0x0500,
    CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN = 0x0510,
    CPTRA_SS_MANUF_TO_PROD_TOKEN = 0x0520,
    CPTRA_SS_PROD_TO_PROD_END_TOKEN = 0x0530,
    CPTRA_SS_RMA_TOKEN = 0x0540,
    // SVN_PARTITION
    CPTRA_CORE_FMC_KEY_MANIFEST_SVN = 0x0558,
    CPTRA_CORE_RUNTIME_SVN = 0x055C,
    CPTRA_CORE_SOC_MANIFEST_SVN = 0x056C,
    CPTRA_CORE_SOC_MANIFEST_MAX_SVN = 0x057C,
    // VENDOR_TEST_PARTITION
    VENDOR_TEST = 0x0580,
    // VENDOR_HASHES_MANUF_PARTITION
    CPTRA_CORE_VENDOR_PK_HASH_0 = 0x05C0,
    CPTRA_CORE_PQC_KEY_TYPE_0 = 0x05F0,
    // VENDOR_HASHES_PROD_PARTITION
    CPTRA_SS_OWNER_PK_HASH = 0x0600,
    CPTRA_SS_OWNER_PQC_KEY_TYPE = 0x0630,
    CPTRA_SS_OWNER_PK_HASH_VALID = 0x0631,
    CPTRA_CORE_VENDOR_PK_HASH_1 = 0x0632,
    CPTRA_CORE_PQC_KEY_TYPE_1 = 0x0662,
    CPTRA_CORE_VENDOR_PK_HASH_2 = 0x0663,
    CPTRA_CORE_PQC_KEY_TYPE_2 = 0x0693,
    CPTRA_CORE_VENDOR_PK_HASH_3 = 0x0694,
    CPTRA_CORE_PQC_KEY_TYPE_3 = 0x06C4,
    CPTRA_CORE_VENDOR_PK_HASH_4 = 0x06C5,
    CPTRA_CORE_PQC_KEY_TYPE_4 = 0x06F5,
    CPTRA_CORE_VENDOR_PK_HASH_5 = 0x06F6,
    CPTRA_CORE_PQC_KEY_TYPE_5 = 0x0726,
    CPTRA_CORE_VENDOR_PK_HASH_6 = 0x0727,
    CPTRA_CORE_PQC_KEY_TYPE_6 = 0x0757,
    CPTRA_CORE_VENDOR_PK_HASH_7 = 0x0758,
    CPTRA_CORE_PQC_KEY_TYPE_7 = 0x0788,
    CPTRA_CORE_VENDOR_PK_HASH_8 = 0x0789,
    CPTRA_CORE_PQC_KEY_TYPE_8 = 0x07B9,
    CPTRA_CORE_VENDOR_PK_HASH_9 = 0x07BA,
    CPTRA_CORE_PQC_KEY_TYPE_9 = 0x07EA,
    CPTRA_CORE_VENDOR_PK_HASH_10 = 0x07EB,
    CPTRA_CORE_PQC_KEY_TYPE_10 = 0x081B,
    CPTRA_CORE_VENDOR_PK_HASH_11 = 0x081C,
    CPTRA_CORE_PQC_KEY_TYPE_11 = 0x084C,
    CPTRA_CORE_VENDOR_PK_HASH_12 = 0x084D,
    CPTRA_CORE_PQC_KEY_TYPE_12 = 0x087D,
    CPTRA_CORE_VENDOR_PK_HASH_13 = 0x087E,
    CPTRA_CORE_PQC_KEY_TYPE_13 = 0x08AE,
    CPTRA_CORE_VENDOR_PK_HASH_14 = 0x08AF,
    CPTRA_CORE_PQC_KEY_TYPE_14 = 0x08DF,
    CPTRA_CORE_VENDOR_PK_HASH_15 = 0x08E0,
    CPTRA_CORE_PQC_KEY_TYPE_15 = 0x0910,
    CPTRA_CORE_VENDOR_PK_HASH_VALID = 0x0911,
    // VENDOR_REVOCATIONS_PROD_PARTITION
    CPTRA_SS_OWNER_ECC_REVOCATION = 0x0920,
    CPTRA_SS_OWNER_LMS_REVOCATION = 0x0921,
    CPTRA_SS_OWNER_MLDSA_REVOCATION = 0x0925,
    CPTRA_CORE_ECC_REVOCATION_0 = 0x0929,
    CPTRA_CORE_LMS_REVOCATION_0 = 0x092A,
    CPTRA_CORE_MLDSA_REVOCATION_0 = 0x092E,
    CPTRA_CORE_ECC_REVOCATION_1 = 0x0932,
    CPTRA_CORE_LMS_REVOCATION_1 = 0x0933,
    CPTRA_CORE_MLDSA_REVOCATION_1 = 0x0937,
    CPTRA_CORE_ECC_REVOCATION_2 = 0x093B,
    CPTRA_CORE_LMS_REVOCATION_2 = 0x093C,
    CPTRA_CORE_MLDSA_REVOCATION_2 = 0x0940,
    CPTRA_CORE_ECC_REVOCATION_3 = 0x0944,
    CPTRA_CORE_LMS_REVOCATION_3 = 0x0945,
    CPTRA_CORE_MLDSA_REVOCATION_3 = 0x0949,
    CPTRA_CORE_ECC_REVOCATION_4 = 0x094D,
    CPTRA_CORE_LMS_REVOCATION_4 = 0x094E,
    CPTRA_CORE_MLDSA_REVOCATION_4 = 0x0952,
    CPTRA_CORE_ECC_REVOCATION_5 = 0x0956,
    CPTRA_CORE_LMS_REVOCATION_5 = 0x0957,
    CPTRA_CORE_MLDSA_REVOCATION_5 = 0x095B,
    CPTRA_CORE_ECC_REVOCATION_6 = 0x095F,
    CPTRA_CORE_LMS_REVOCATION_6 = 0x0960,
    CPTRA_CORE_MLDSA_REVOCATION_6 = 0x0964,
    CPTRA_CORE_ECC_REVOCATION_7 = 0x0968,
    CPTRA_CORE_LMS_REVOCATION_7 = 0x0969,
    CPTRA_CORE_MLDSA_REVOCATION_7 = 0x096D,
    CPTRA_CORE_ECC_REVOCATION_8 = 0x0971,
    CPTRA_CORE_LMS_REVOCATION_8 = 0x0972,
    CPTRA_CORE_MLDSA_REVOCATION_8 = 0x0976,
    CPTRA_CORE_ECC_REVOCATION_9 = 0x097A,
    CPTRA_CORE_LMS_REVOCATION_9 = 0x097B,
    CPTRA_CORE_MLDSA_REVOCATION_9 = 0x097F,
    CPTRA_CORE_ECC_REVOCATION_10 = 0x0983,
    CPTRA_CORE_LMS_REVOCATION_10 = 0x0984,
    CPTRA_CORE_MLDSA_REVOCATION_10 = 0x0988,
    CPTRA_CORE_ECC_REVOCATION_11 = 0x098C,
    CPTRA_CORE_LMS_REVOCATION_11 = 0x098D,
    CPTRA_CORE_MLDSA_REVOCATION_11 = 0x0991,
    CPTRA_CORE_ECC_REVOCATION_12 = 0x0995,
    CPTRA_CORE_LMS_REVOCATION_12 = 0x0996,
    CPTRA_CORE_MLDSA_REVOCATION_12 = 0x099A,
    CPTRA_CORE_ECC_REVOCATION_13 = 0x099E,
    CPTRA_CORE_LMS_REVOCATION_13 = 0x099F,
    CPTRA_CORE_MLDSA_REVOCATION_13 = 0x09A3,
    CPTRA_CORE_ECC_REVOCATION_14 = 0x09A7,
    CPTRA_CORE_LMS_REVOCATION_14 = 0x09A8,
    CPTRA_CORE_MLDSA_REVOCATION_14 = 0x09AC,
    CPTRA_CORE_ECC_REVOCATION_15 = 0x09B0,
    CPTRA_CORE_LMS_REVOCATION_15 = 0x09B1,
    CPTRA_CORE_MLDSA_REVOCATION_15 = 0x09B5,
    // VENDOR_SECRET_PROD_PARTITION
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_0 = 0x09C8,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_1 = 0x09E8,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_2 = 0x0A08,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_3 = 0x0A28,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_4 = 0x0A48,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_5 = 0x0A68,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_6 = 0x0A88,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_7 = 0x0AA8,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_8 = 0x0AC8,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_9 = 0x0AE8,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_10 = 0x0B08,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_11 = 0x0B28,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_12 = 0x0B48,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_13 = 0x0B68,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_14 = 0x0B88,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_15 = 0x0BA8,
    // VENDOR_NON_SECRET_PROD_PARTITION
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_0 = 0x0BD0,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_1 = 0x0BF0,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_2 = 0x0C10,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_3 = 0x0C30,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_4 = 0x0C50,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_5 = 0x0C70,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_6 = 0x0C90,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_7 = 0x0CB0,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_8 = 0x0CD0,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_9 = 0x0CF0,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_10 = 0x0D10,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_11 = 0x0D30,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_12 = 0x0D50,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_13 = 0x0D70,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_14 = 0x0D90,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_15 = 0x0DB0,
    // LIFE_CYCLE
    LC_TRANSITION_CNT = 0x0FA8,
    LC_STATE = 0x0FD8
} fuse_k;

typedef enum {
    SW_TEST_UNLOCK_PARTITION,
    SECRET_MANUF_PARTITION,
    SECRET_PROD_PARTITION_0,
    SECRET_PROD_PARTITION_1,
    SECRET_PROD_PARTITION_2,
    SECRET_PROD_PARTITION_3,
    SW_MANUF_PARTITION,
    SECRET_LC_TRANSITION_PARTITION,
    SVN_PARTITION,
    VENDOR_TEST_PARTITION,
    VENDOR_HASHES_MANUF_PARTITION,
    VENDOR_HASHES_PROD_PARTITION,
    VENDOR_REVOCATIONS_PROD_PARTITION,
    VENDOR_SECRET_PROD_PARTITION,
    VENDOR_NON_SECRET_PROD_PARTITION,
    LIFE_CYCLE
} partition_k;

typedef struct {
    uint32_t index;
    uint32_t address;
    uint32_t digest_address;
    uint32_t variant;
    uint32_t granularity;
    bool is_secret;
    bool hw_digest;
    bool sw_digest;
    bool has_read_lock;
    bool has_ecc;
    bool is_lifecycle;
    bool is_clearable;
    uint32_t lc_phase;
    uint32_t num_fuses;
    uint32_t *fuses;
} partition_t;

#define NUM_PARTITIONS 16

uint32_t sw_test_unlock_partition_fuses[] = {
    CPTRA_SS_MANUF_DEBUG_UNLOCK_TOKEN
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
uint32_t vendor_revocations_prod_partition_fuses[] = {
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
        .index = 0,
        .address = 0x0000,
        .digest_address = 0x0040,
        .variant = 0,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = true,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 16,
        .is_lifecycle = false,
        .is_clearable = false,
        .num_fuses = 1,
        .fuses = sw_test_unlock_partition_fuses
    },
    // SECRET_MANUF_PARTITION
    {
        .index = 1,
        .address = 0x0048,
        .digest_address = 0x0088,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 16,
        .is_lifecycle = false,
        .is_clearable = false,
        .num_fuses = 1,
        .fuses = secret_manuf_partition_fuses
    },
    // SECRET_PROD_PARTITION_0
    {
        .index = 2,
        .address = 0x0090,
        .digest_address = 0x0098,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .is_clearable = false,
        .num_fuses = 1,
        .fuses = secret_prod_partition_0_fuses
    },
    // SECRET_PROD_PARTITION_1
    {
        .index = 3,
        .address = 0x00A0,
        .digest_address = 0x00A8,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .is_clearable = false,
        .num_fuses = 1,
        .fuses = secret_prod_partition_1_fuses
    },
    // SECRET_PROD_PARTITION_2
    {
        .index = 4,
        .address = 0x00B0,
        .digest_address = 0x00B8,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .is_clearable = false,
        .num_fuses = 1,
        .fuses = secret_prod_partition_2_fuses
    },
    // SECRET_PROD_PARTITION_3
    {
        .index = 5,
        .address = 0x00C0,
        .digest_address = 0x00C8,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .is_clearable = false,
        .num_fuses = 1,
        .fuses = secret_prod_partition_3_fuses
    },
    // SW_MANUF_PARTITION
    {
        .index = 6,
        .address = 0x00D0,
        .digest_address = 0x0498,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = true,
        .lc_phase = 16,
        .is_lifecycle = false,
        .is_clearable = false,
        .num_fuses = 13,
        .fuses = sw_manuf_partition_fuses
    },
    // SECRET_LC_TRANSITION_PARTITION
    {
        .index = 7,
        .address = 0x04A0,
        .digest_address = 0x0550,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 1,
        .is_lifecycle = false,
        .is_clearable = true,
        .num_fuses = 11,
        .fuses = secret_lc_transition_partition_fuses
    },
    // SVN_PARTITION
    {
        .index = 8,
        .address = 0x0558,
        .digest_address = 0x0000,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = false,
        .has_read_lock = true,
        .has_ecc = false,
        .lc_phase = 17,
        .is_lifecycle = false,
        .is_clearable = false,
        .num_fuses = 3,
        .fuses = svn_partition_fuses
    },
    // VENDOR_TEST_PARTITION
    {
        .index = 9,
        .address = 0x0580,
        .digest_address = 0x05B8,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = false,
        .lc_phase = 17,
        .is_lifecycle = false,
        .is_clearable = false,
        .num_fuses = 1,
        .fuses = vendor_test_partition_fuses
    },
    // VENDOR_HASHES_MANUF_PARTITION
    {
        .index = 10,
        .address = 0x05C0,
        .digest_address = 0x05F8,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = false,
        .lc_phase = 16,
        .is_lifecycle = false,
        .is_clearable = false,
        .num_fuses = 2,
        .fuses = vendor_hashes_manuf_partition_fuses
    },
    // VENDOR_HASHES_PROD_PARTITION
    {
        .index = 11,
        .address = 0x0600,
        .digest_address = 0x0918,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = false,
        .lc_phase = 17,
        .is_lifecycle = false,
        .is_clearable = false,
        .num_fuses = 34,
        .fuses = vendor_hashes_prod_partition_fuses
    },
    // VENDOR_REVOCATIONS_PROD_PARTITION
    {
        .index = 12,
        .address = 0x0920,
        .digest_address = 0x09C0,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = false,
        .lc_phase = 17,
        .is_lifecycle = false,
        .is_clearable = false,
        .num_fuses = 51,
        .fuses = vendor_revocations_prod_partition_fuses
    },
    // VENDOR_SECRET_PROD_PARTITION
    {
        .index = 13,
        .address = 0x09C8,
        .digest_address = 0x0BC8,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .is_clearable = false,
        .num_fuses = 16,
        .fuses = vendor_secret_prod_partition_fuses
    },
    // VENDOR_NON_SECRET_PROD_PARTITION
    {
        .index = 14,
        .address = 0x0BD0,
        .digest_address = 0x0FA0,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .is_clearable = false,
        .num_fuses = 16,
        .fuses = vendor_non_secret_prod_partition_fuses
    },
    // LIFE_CYCLE
    {
        .index = 15,
        .address = 0x0FA8,
        .digest_address = 0x0000,
        .variant = 2,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 0,
        .is_lifecycle = true,
        .is_clearable = false,
        .num_fuses = 1,
        .fuses = life_cycle_fuses
    },
};

#endif // FUSE_CTRL_MMAP_HEADER