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
    CPTRA_CORE_IDEVID_CERT_IDEVID_ATTR = 0x00D4,
    SOC_SPECIFIC_IDEVID_CERTIFICATE = 0x0134,
    CPTRA_CORE_IDEVID_MANUF_HSM_IDENTIFIER = 0x0138,
    CPTRA_CORE_SOC_STEPPING_ID = 0x0148,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_0 = 0x014C,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_1 = 0x017C,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_2 = 0x01AC,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_3 = 0x01DC,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_4 = 0x020C,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_5 = 0x023C,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_6 = 0x026C,
    CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_7 = 0x029C,
    // SECRET_LC_TRANSITION_PARTITION
    CPTRA_SS_TEST_UNLOCK_TOKEN_1 = 0x02D8,
    CPTRA_SS_TEST_UNLOCK_TOKEN_2 = 0x02E8,
    CPTRA_SS_TEST_UNLOCK_TOKEN_3 = 0x02F8,
    CPTRA_SS_TEST_UNLOCK_TOKEN_4 = 0x0308,
    CPTRA_SS_TEST_UNLOCK_TOKEN_5 = 0x0318,
    CPTRA_SS_TEST_UNLOCK_TOKEN_6 = 0x0328,
    CPTRA_SS_TEST_UNLOCK_TOKEN_7 = 0x0338,
    CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN = 0x0348,
    CPTRA_SS_MANUF_TO_PROD_TOKEN = 0x0358,
    CPTRA_SS_PROD_TO_PROD_END_TOKEN = 0x0368,
    CPTRA_SS_RMA_TOKEN = 0x0378,
    // SVN_PARTITION
    CPTRA_CORE_FMC_KEY_MANIFEST_SVN = 0x0390,
    CPTRA_CORE_RUNTIME_SVN = 0x0394,
    CPTRA_CORE_SOC_MANIFEST_SVN = 0x03A4,
    CPTRA_CORE_SOC_MANIFEST_MAX_SVN = 0x03B4,
    // VENDOR_TEST_PARTITION
    VENDOR_TEST = 0x03B8,
    // VENDOR_HASHES_MANUF_PARTITION
    CPTRA_CORE_VENDOR_PK_HASH_0 = 0x03F8,
    CPTRA_CORE_PQC_KEY_TYPE_0 = 0x0428,
    // VENDOR_HASHES_PROD_PARTITION
    CPTRA_SS_OWNER_PK_HASH = 0x0438,
    CPTRA_SS_OWNER_PQC_KEY_TYPE = 0x0468,
    CPTRA_SS_OWNER_PK_HASH_VALID = 0x046C,
    CPTRA_CORE_VENDOR_PK_HASH_1 = 0x0470,
    CPTRA_CORE_PQC_KEY_TYPE_1 = 0x04A0,
    CPTRA_CORE_VENDOR_PK_HASH_2 = 0x04A4,
    CPTRA_CORE_PQC_KEY_TYPE_2 = 0x04D4,
    CPTRA_CORE_VENDOR_PK_HASH_3 = 0x04D8,
    CPTRA_CORE_PQC_KEY_TYPE_3 = 0x0508,
    CPTRA_CORE_VENDOR_PK_HASH_4 = 0x050C,
    CPTRA_CORE_PQC_KEY_TYPE_4 = 0x053C,
    CPTRA_CORE_VENDOR_PK_HASH_5 = 0x0540,
    CPTRA_CORE_PQC_KEY_TYPE_5 = 0x0570,
    CPTRA_CORE_VENDOR_PK_HASH_6 = 0x0574,
    CPTRA_CORE_PQC_KEY_TYPE_6 = 0x05A4,
    CPTRA_CORE_VENDOR_PK_HASH_7 = 0x05A8,
    CPTRA_CORE_PQC_KEY_TYPE_7 = 0x05D8,
    CPTRA_CORE_VENDOR_PK_HASH_8 = 0x05DC,
    CPTRA_CORE_PQC_KEY_TYPE_8 = 0x060C,
    CPTRA_CORE_VENDOR_PK_HASH_9 = 0x0610,
    CPTRA_CORE_PQC_KEY_TYPE_9 = 0x0640,
    CPTRA_CORE_VENDOR_PK_HASH_10 = 0x0644,
    CPTRA_CORE_PQC_KEY_TYPE_10 = 0x0674,
    CPTRA_CORE_VENDOR_PK_HASH_11 = 0x0678,
    CPTRA_CORE_PQC_KEY_TYPE_11 = 0x06A8,
    CPTRA_CORE_VENDOR_PK_HASH_12 = 0x06AC,
    CPTRA_CORE_PQC_KEY_TYPE_12 = 0x06DC,
    CPTRA_CORE_VENDOR_PK_HASH_13 = 0x06E0,
    CPTRA_CORE_PQC_KEY_TYPE_13 = 0x0710,
    CPTRA_CORE_VENDOR_PK_HASH_14 = 0x0714,
    CPTRA_CORE_PQC_KEY_TYPE_14 = 0x0744,
    CPTRA_CORE_VENDOR_PK_HASH_15 = 0x0748,
    CPTRA_CORE_PQC_KEY_TYPE_15 = 0x0778,
    CPTRA_CORE_VENDOR_PK_HASH_VALID = 0x077C,
    // VENDOR_REVOCATIONS_PROD_PARTITION
    CPTRA_SS_OWNER_ECC_REVOCATION = 0x0798,
    CPTRA_SS_OWNER_LMS_REVOCATION = 0x079C,
    CPTRA_SS_OWNER_MLDSA_REVOCATION = 0x07A0,
    CPTRA_CORE_ECC_REVOCATION_0 = 0x07A4,
    CPTRA_CORE_LMS_REVOCATION_0 = 0x07A8,
    CPTRA_CORE_MLDSA_REVOCATION_0 = 0x07AC,
    CPTRA_CORE_ECC_REVOCATION_1 = 0x07B0,
    CPTRA_CORE_LMS_REVOCATION_1 = 0x07B4,
    CPTRA_CORE_MLDSA_REVOCATION_1 = 0x07B8,
    CPTRA_CORE_ECC_REVOCATION_2 = 0x07BC,
    CPTRA_CORE_LMS_REVOCATION_2 = 0x07C0,
    CPTRA_CORE_MLDSA_REVOCATION_2 = 0x07C4,
    CPTRA_CORE_ECC_REVOCATION_3 = 0x07C8,
    CPTRA_CORE_LMS_REVOCATION_3 = 0x07CC,
    CPTRA_CORE_MLDSA_REVOCATION_3 = 0x07D0,
    CPTRA_CORE_ECC_REVOCATION_4 = 0x07D4,
    CPTRA_CORE_LMS_REVOCATION_4 = 0x07D8,
    CPTRA_CORE_MLDSA_REVOCATION_4 = 0x07DC,
    CPTRA_CORE_ECC_REVOCATION_5 = 0x07E0,
    CPTRA_CORE_LMS_REVOCATION_5 = 0x07E4,
    CPTRA_CORE_MLDSA_REVOCATION_5 = 0x07E8,
    CPTRA_CORE_ECC_REVOCATION_6 = 0x07EC,
    CPTRA_CORE_LMS_REVOCATION_6 = 0x07F0,
    CPTRA_CORE_MLDSA_REVOCATION_6 = 0x07F4,
    CPTRA_CORE_ECC_REVOCATION_7 = 0x07F8,
    CPTRA_CORE_LMS_REVOCATION_7 = 0x07FC,
    CPTRA_CORE_MLDSA_REVOCATION_7 = 0x0800,
    CPTRA_CORE_ECC_REVOCATION_8 = 0x0804,
    CPTRA_CORE_LMS_REVOCATION_8 = 0x0808,
    CPTRA_CORE_MLDSA_REVOCATION_8 = 0x080C,
    CPTRA_CORE_ECC_REVOCATION_9 = 0x0810,
    CPTRA_CORE_LMS_REVOCATION_9 = 0x0814,
    CPTRA_CORE_MLDSA_REVOCATION_9 = 0x0818,
    CPTRA_CORE_ECC_REVOCATION_10 = 0x081C,
    CPTRA_CORE_LMS_REVOCATION_10 = 0x0820,
    CPTRA_CORE_MLDSA_REVOCATION_10 = 0x0824,
    CPTRA_CORE_ECC_REVOCATION_11 = 0x0828,
    CPTRA_CORE_LMS_REVOCATION_11 = 0x082C,
    CPTRA_CORE_MLDSA_REVOCATION_11 = 0x0830,
    CPTRA_CORE_ECC_REVOCATION_12 = 0x0834,
    CPTRA_CORE_LMS_REVOCATION_12 = 0x0838,
    CPTRA_CORE_MLDSA_REVOCATION_12 = 0x083C,
    CPTRA_CORE_ECC_REVOCATION_13 = 0x0840,
    CPTRA_CORE_LMS_REVOCATION_13 = 0x0844,
    CPTRA_CORE_MLDSA_REVOCATION_13 = 0x0848,
    CPTRA_CORE_ECC_REVOCATION_14 = 0x084C,
    CPTRA_CORE_LMS_REVOCATION_14 = 0x0850,
    CPTRA_CORE_MLDSA_REVOCATION_14 = 0x0854,
    CPTRA_CORE_ECC_REVOCATION_15 = 0x0858,
    CPTRA_CORE_LMS_REVOCATION_15 = 0x085C,
    CPTRA_CORE_MLDSA_REVOCATION_15 = 0x0860,
    // VENDOR_SECRET_PROD_PARTITION
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_0 = 0x0870,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_1 = 0x0890,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_2 = 0x08B0,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_3 = 0x08D0,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_4 = 0x08F0,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_5 = 0x0910,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_6 = 0x0930,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_7 = 0x0950,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_8 = 0x0970,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_9 = 0x0990,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_10 = 0x09B0,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_11 = 0x09D0,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_12 = 0x09F0,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_13 = 0x0A10,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_14 = 0x0A30,
    CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_15 = 0x0A50,
    // VENDOR_NON_SECRET_PROD_PARTITION
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_0 = 0x0A80,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_1 = 0x0AA0,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_2 = 0x0AC0,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_3 = 0x0AE0,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_4 = 0x0B00,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_5 = 0x0B20,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_6 = 0x0B40,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_7 = 0x0B60,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_8 = 0x0B80,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_9 = 0x0BA0,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_10 = 0x0BC0,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_11 = 0x0BE0,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_12 = 0x0C00,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_13 = 0x0C20,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_14 = 0x0C40,
    CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_15 = 0x0C60,
    // CPTRA_SS_LOCK_HEK_PROD_0
    CPTRA_SS_LOCK_HEK_PROD_0_RATCHET_SEED = 0x0C88,
    // CPTRA_SS_LOCK_HEK_PROD_1
    CPTRA_SS_LOCK_HEK_PROD_1_RATCHET_SEED = 0x0CB8,
    // CPTRA_SS_LOCK_HEK_PROD_2
    CPTRA_SS_LOCK_HEK_PROD_2_RATCHET_SEED = 0x0CE8,
    // CPTRA_SS_LOCK_HEK_PROD_3
    CPTRA_SS_LOCK_HEK_PROD_3_RATCHET_SEED = 0x0D18,
    // CPTRA_SS_LOCK_HEK_PROD_4
    CPTRA_SS_LOCK_HEK_PROD_4_RATCHET_SEED = 0x0D48,
    // CPTRA_SS_LOCK_HEK_PROD_5
    CPTRA_SS_LOCK_HEK_PROD_5_RATCHET_SEED = 0x0D78,
    // CPTRA_SS_LOCK_HEK_PROD_6
    CPTRA_SS_LOCK_HEK_PROD_6_RATCHET_SEED = 0x0DA8,
    // CPTRA_SS_LOCK_HEK_PROD_7
    CPTRA_SS_LOCK_HEK_PROD_7_RATCHET_SEED = 0x0DD8,
    // LIFE_CYCLE
    LC_TRANSITION_CNT = 0x0E08,
    LC_STATE = 0x0E38
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
    CPTRA_SS_LOCK_HEK_PROD_0,
    CPTRA_SS_LOCK_HEK_PROD_1,
    CPTRA_SS_LOCK_HEK_PROD_2,
    CPTRA_SS_LOCK_HEK_PROD_3,
    CPTRA_SS_LOCK_HEK_PROD_4,
    CPTRA_SS_LOCK_HEK_PROD_5,
    CPTRA_SS_LOCK_HEK_PROD_6,
    CPTRA_SS_LOCK_HEK_PROD_7,
    LIFE_CYCLE
} partition_k;

typedef struct {
    uint32_t index;
    uint32_t address;
    uint32_t digest_address;
    uint32_t zer_address;
    uint32_t variant;
    uint32_t granularity;
    bool is_secret;
    bool hw_digest;
    bool sw_digest;
    bool has_read_lock;
    bool has_ecc;
    bool is_lifecycle;
    uint32_t lc_phase;
    uint32_t num_fuses;
    uint32_t *fuses;
} partition_t;

#define NUM_PARTITIONS 24

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
uint32_t cptra_ss_lock_hek_prod_0_fuses[] = {
    CPTRA_SS_LOCK_HEK_PROD_0_RATCHET_SEED
};
uint32_t cptra_ss_lock_hek_prod_1_fuses[] = {
    CPTRA_SS_LOCK_HEK_PROD_1_RATCHET_SEED
};
uint32_t cptra_ss_lock_hek_prod_2_fuses[] = {
    CPTRA_SS_LOCK_HEK_PROD_2_RATCHET_SEED
};
uint32_t cptra_ss_lock_hek_prod_3_fuses[] = {
    CPTRA_SS_LOCK_HEK_PROD_3_RATCHET_SEED
};
uint32_t cptra_ss_lock_hek_prod_4_fuses[] = {
    CPTRA_SS_LOCK_HEK_PROD_4_RATCHET_SEED
};
uint32_t cptra_ss_lock_hek_prod_5_fuses[] = {
    CPTRA_SS_LOCK_HEK_PROD_5_RATCHET_SEED
};
uint32_t cptra_ss_lock_hek_prod_6_fuses[] = {
    CPTRA_SS_LOCK_HEK_PROD_6_RATCHET_SEED
};
uint32_t cptra_ss_lock_hek_prod_7_fuses[] = {
    CPTRA_SS_LOCK_HEK_PROD_7_RATCHET_SEED
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
        .zer_address = 0x0000,
        .variant = 0,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = true,
        .sw_digest = false,
        .has_read_lock = false,
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
        .zer_address = 0x0000,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 16,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = secret_manuf_partition_fuses
    },
    // SECRET_PROD_PARTITION_0
    {
        .index = 2,
        .address = 0x0090,
        .digest_address = 0x0098,
        .zer_address = 0x0000,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = secret_prod_partition_0_fuses
    },
    // SECRET_PROD_PARTITION_1
    {
        .index = 3,
        .address = 0x00A0,
        .digest_address = 0x00A8,
        .zer_address = 0x0000,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = secret_prod_partition_1_fuses
    },
    // SECRET_PROD_PARTITION_2
    {
        .index = 4,
        .address = 0x00B0,
        .digest_address = 0x00B8,
        .zer_address = 0x0000,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = secret_prod_partition_2_fuses
    },
    // SECRET_PROD_PARTITION_3
    {
        .index = 5,
        .address = 0x00C0,
        .digest_address = 0x00C8,
        .zer_address = 0x0000,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = secret_prod_partition_3_fuses
    },
    // SW_MANUF_PARTITION
    {
        .index = 6,
        .address = 0x00D0,
        .digest_address = 0x02D0,
        .zer_address = 0x0000,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = true,
        .lc_phase = 16,
        .is_lifecycle = false,
        .num_fuses = 13,
        .fuses = sw_manuf_partition_fuses
    },
    // SECRET_LC_TRANSITION_PARTITION
    {
        .index = 7,
        .address = 0x02D8,
        .digest_address = 0x0388,
        .zer_address = 0x0000,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 1,
        .is_lifecycle = false,
        .num_fuses = 11,
        .fuses = secret_lc_transition_partition_fuses
    },
    // SVN_PARTITION
    {
        .index = 8,
        .address = 0x0390,
        .digest_address = 0x0000,
        .zer_address = 0x0000,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = false,
        .has_read_lock = true,
        .has_ecc = false,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 3,
        .fuses = svn_partition_fuses
    },
    // VENDOR_TEST_PARTITION
    {
        .index = 9,
        .address = 0x03B8,
        .digest_address = 0x03F0,
        .zer_address = 0x0000,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = false,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 1,
        .fuses = vendor_test_partition_fuses
    },
    // VENDOR_HASHES_MANUF_PARTITION
    {
        .index = 10,
        .address = 0x03F8,
        .digest_address = 0x0430,
        .zer_address = 0x0000,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = false,
        .lc_phase = 16,
        .is_lifecycle = false,
        .num_fuses = 2,
        .fuses = vendor_hashes_manuf_partition_fuses
    },
    // VENDOR_HASHES_PROD_PARTITION
    {
        .index = 11,
        .address = 0x0438,
        .digest_address = 0x0790,
        .zer_address = 0x0000,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = false,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 34,
        .fuses = vendor_hashes_prod_partition_fuses
    },
    // VENDOR_REVOCATIONS_PROD_PARTITION
    {
        .index = 12,
        .address = 0x0798,
        .digest_address = 0x0868,
        .zer_address = 0x0000,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = false,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 51,
        .fuses = vendor_revocations_prod_partition_fuses
    },
    // VENDOR_SECRET_PROD_PARTITION
    {
        .index = 13,
        .address = 0x0870,
        .digest_address = 0x0A70,
        .zer_address = 0x0A78,
        .variant = 0,
        .granularity = 64,
        .is_secret = true,
        .hw_digest = true,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 17,
        .fuses = vendor_secret_prod_partition_fuses
    },
    // VENDOR_NON_SECRET_PROD_PARTITION
    {
        .index = 14,
        .address = 0x0A80,
        .digest_address = 0x0C80,
        .zer_address = 0x0000,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 16,
        .fuses = vendor_non_secret_prod_partition_fuses
    },
    // CPTRA_SS_LOCK_HEK_PROD_0
    {
        .index = 15,
        .address = 0x0C88,
        .digest_address = 0x0CA8,
        .zer_address = 0x0CB0,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 2,
        .fuses = cptra_ss_lock_hek_prod_0_fuses
    },
    // CPTRA_SS_LOCK_HEK_PROD_1
    {
        .index = 16,
        .address = 0x0CB8,
        .digest_address = 0x0CD8,
        .zer_address = 0x0CE0,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 2,
        .fuses = cptra_ss_lock_hek_prod_1_fuses
    },
    // CPTRA_SS_LOCK_HEK_PROD_2
    {
        .index = 17,
        .address = 0x0CE8,
        .digest_address = 0x0D08,
        .zer_address = 0x0D10,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 2,
        .fuses = cptra_ss_lock_hek_prod_2_fuses
    },
    // CPTRA_SS_LOCK_HEK_PROD_3
    {
        .index = 18,
        .address = 0x0D18,
        .digest_address = 0x0D38,
        .zer_address = 0x0D40,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 2,
        .fuses = cptra_ss_lock_hek_prod_3_fuses
    },
    // CPTRA_SS_LOCK_HEK_PROD_4
    {
        .index = 19,
        .address = 0x0D48,
        .digest_address = 0x0D68,
        .zer_address = 0x0D70,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 2,
        .fuses = cptra_ss_lock_hek_prod_4_fuses
    },
    // CPTRA_SS_LOCK_HEK_PROD_5
    {
        .index = 20,
        .address = 0x0D78,
        .digest_address = 0x0D98,
        .zer_address = 0x0DA0,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 2,
        .fuses = cptra_ss_lock_hek_prod_5_fuses
    },
    // CPTRA_SS_LOCK_HEK_PROD_6
    {
        .index = 21,
        .address = 0x0DA8,
        .digest_address = 0x0DC8,
        .zer_address = 0x0DD0,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 2,
        .fuses = cptra_ss_lock_hek_prod_6_fuses
    },
    // CPTRA_SS_LOCK_HEK_PROD_7
    {
        .index = 22,
        .address = 0x0DD8,
        .digest_address = 0x0DF8,
        .zer_address = 0x0E00,
        .variant = 1,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = true,
        .has_read_lock = true,
        .has_ecc = true,
        .lc_phase = 17,
        .is_lifecycle = false,
        .num_fuses = 2,
        .fuses = cptra_ss_lock_hek_prod_7_fuses
    },
    // LIFE_CYCLE
    {
        .index = 23,
        .address = 0x0E08,
        .digest_address = 0x0000,
        .zer_address = 0x0000,
        .variant = 2,
        .granularity = 32,
        .is_secret = false,
        .hw_digest = false,
        .sw_digest = false,
        .has_read_lock = false,
        .has_ecc = true,
        .lc_phase = 0,
        .is_lifecycle = true,
        .num_fuses = 1,
        .fuses = life_cycle_fuses
    },
};

#endif // FUSE_CTRL_MMAP_HEADER