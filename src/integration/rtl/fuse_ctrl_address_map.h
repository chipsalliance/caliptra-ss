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
#ifndef FUSE_CTRL_ADDRMAP_HEADER
#define FUSE_CTRL_ADDRMAP_HEADER

#define FUSE_CTRL_BASE_ADDR                             (0x70000000)
#define FUSE_CTRL_INTR_STATE                            (FUSE_CTRL_BASE_ADDR + 0x00)
#define FUSE_CTRL_INTR_ENABLE                           (FUSE_CTRL_BASE_ADDR + 0x04)
#define FUSE_CTRL_INTR_TEST                             (FUSE_CTRL_BASE_ADDR + 0x08)
#define FUSE_CTRL_ALERT_TEST                            (FUSE_CTRL_BASE_ADDR + 0x0C)
#define FUSE_CTRL_STATUS                                (FUSE_CTRL_BASE_ADDR + 0x10)
#define FUSE_CTRL_ERR_CODE_0                            (FUSE_CTRL_BASE_ADDR + 0x14)
#define FUSE_CTRL_ERR_CODE_1                            (FUSE_CTRL_BASE_ADDR + 0x18)
#define FUSE_CTRL_ERR_CODE_2                            (FUSE_CTRL_BASE_ADDR + 0x1C)
#define FUSE_CTRL_ERR_CODE_3                            (FUSE_CTRL_BASE_ADDR + 0x20)
#define FUSE_CTRL_ERR_CODE_4                            (FUSE_CTRL_BASE_ADDR + 0x24)
#define FUSE_CTRL_ERR_CODE_5                            (FUSE_CTRL_BASE_ADDR + 0x28)
#define FUSE_CTRL_ERR_CODE_6                            (FUSE_CTRL_BASE_ADDR + 0x2C)
#define FUSE_CTRL_ERR_CODE_7                            (FUSE_CTRL_BASE_ADDR + 0x30)
#define FUSE_CTRL_ERR_CODE_8                            (FUSE_CTRL_BASE_ADDR + 0x34)
#define FUSE_CTRL_ERR_CODE_9                            (FUSE_CTRL_BASE_ADDR + 0x38)
#define FUSE_CTRL_ERR_CODE_10                           (FUSE_CTRL_BASE_ADDR + 0x3C)
#define FUSE_CTRL_ERR_CODE_11                           (FUSE_CTRL_BASE_ADDR + 0x40)
#define FUSE_CTRL_ERR_CODE_12                           (FUSE_CTRL_BASE_ADDR + 0x44)
#define FUSE_CTRL_ERR_CODE_13                           (FUSE_CTRL_BASE_ADDR + 0x48)
#define FUSE_CTRL_ERR_CODE_14                           (FUSE_CTRL_BASE_ADDR + 0x4C)
#define FUSE_CTRL_ERR_CODE_15                           (FUSE_CTRL_BASE_ADDR + 0x50)
#define FUSE_CTRL_ERR_CODE_16                           (FUSE_CTRL_BASE_ADDR + 0x54)
#define FUSE_CTRL_ERR_CODE_16                           (FUSE_CTRL_BASE_ADDR + 0x58)
#define FUSE_CTRL_DIRECT_ACCESS_REGWEN                  (FUSE_CTRL_BASE_ADDR + 0x5C)
#define FUSE_CTRL_DIRECT_ACCESS_CMD                     (FUSE_CTRL_BASE_ADDR + 0x60)
#define FUSE_CTRL_DIRECT_ACCESS_ADDRESS                 (FUSE_CTRL_BASE_ADDR + 0x64)
#define FUSE_CTRL_DIRECT_ACCESS_WDATA_0                 (FUSE_CTRL_BASE_ADDR + 0x68)
#define FUSE_CTRL_DIRECT_ACCESS_WDATA_1                 (FUSE_CTRL_BASE_ADDR + 0x6C)
#define FUSE_CTRL_DIRECT_ACCESS_RDATA_0                 (FUSE_CTRL_BASE_ADDR + 0x70)
#define FUSE_CTRL_DIRECT_ACCESS_RDATA_1                 (FUSE_CTRL_BASE_ADDR + 0x74)
#define FUSE_CTRL_CHECK_TRIGGER_REGWEN                  (FUSE_CTRL_BASE_ADDR + 0x78)
#define FUSE_CTRL_CHECK_TRIGGER                         (FUSE_CTRL_BASE_ADDR + 0x7C)
#define FUSE_CTRL_CHECK_REGWEN                          (FUSE_CTRL_BASE_ADDR + 0x80)
#define FUSE_CTRL_CHECK_TIMEOUT                         (FUSE_CTRL_BASE_ADDR + 0x84)
#define FUSE_CTRL_INTEGRITY_CHECK_PERIOD                (FUSE_CTRL_BASE_ADDR + 0x88)
#define FUSE_CTRL_CONSISTENCY_CHECK_PERIOD              (FUSE_CTRL_BASE_ADDR + 0x8C)

// #define FUSE_CTRL_VENDOR_TEST_READ_LOCK                 (FUSE_CTRL_BASE_ADDR + 0x88)
// #define FUSE_CTRL_CREATOR_SW_CFG_READ_LOCK              (FUSE_CTRL_BASE_ADDR + 0x8C)
// #define FUSE_CTRL_OWNER_SW_CFG_READ_LOCK                (FUSE_CTRL_BASE_ADDR + 0x84)
// #define FUSE_CTRL_ROT_CREATOR_AUTH_CODESIGN_READ_LOCK   (FUSE_CTRL_BASE_ADDR + 0x88)
// #define FUSE_CTRL_ROT_CREATOR_AUTH_STATE_READ_LOCK      (FUSE_CTRL_BASE_ADDR + 0x8C)
// #define FUSE_CTRL_VENDOR_TEST_DIGEST_0                  (FUSE_CTRL_BASE_ADDR + 0x90)
// #define FUSE_CTRL_VENDOR_TEST_DIGEST_1                  (FUSE_CTRL_BASE_ADDR + 0x94)
// #define FUSE_CTRL_CREATOR_SW_CFG_DIGEST_0               (FUSE_CTRL_BASE_ADDR + 0x98)
// #define FUSE_CTRL_CREATOR_SW_CFG_DIGEST_1               (FUSE_CTRL_BASE_ADDR + 0x9C)
// #define FUSE_CTRL_OWNER_SW_CFG_DIGEST_0                 (FUSE_CTRL_BASE_ADDR + 0xA0)
// #define FUSE_CTRL_OWNER_SW_CFG_DIGEST_1                 (FUSE_CTRL_BASE_ADDR + 0xA4)
// #define FUSE_CTRL_ROT_CREATOR_AUTH_CODESIGN_DIGEST_0    (FUSE_CTRL_BASE_ADDR + 0xA8)
// #define FUSE_CTRL_ROT_CREATOR_AUTH_CODESIGN_DIGEST_1    (FUSE_CTRL_BASE_ADDR + 0xAC)
// #define FUSE_CTRL_ROT_CREATOR_AUTH_STATE_DIGEST_0       (FUSE_CTRL_BASE_ADDR + 0xB0)
// #define FUSE_CTRL_ROT_CREATOR_AUTH_STATE_DIGEST_1       (FUSE_CTRL_BASE_ADDR + 0xB4)
// #define FUSE_CTRL_HW_CFG0_DIGEST_0                      (FUSE_CTRL_BASE_ADDR + 0xB8)
// #define FUSE_CTRL_HW_CFG0_DIGEST_1                      (FUSE_CTRL_BASE_ADDR + 0xBC)
// #define FUSE_CTRL_HW_CFG1_DIGEST_0                      (FUSE_CTRL_BASE_ADDR + 0xC0)
// #define FUSE_CTRL_HW_CFG1_DIGEST_1                      (FUSE_CTRL_BASE_ADDR + 0xC4)
// #define FUSE_CTRL_SECRET0_DIGEST_0                      (FUSE_CTRL_BASE_ADDR + 0xC8)
// #define FUSE_CTRL_SECRET0_DIGEST_1                      (FUSE_CTRL_BASE_ADDR + 0xCC)
// #define FUSE_CTRL_SECRET1_DIGEST_0                      (FUSE_CTRL_BASE_ADDR + 0xD0)
// #define FUSE_CTRL_SECRET1_DIGEST_1                      (FUSE_CTRL_BASE_ADDR + 0xD4)
// #define FUSE_CTRL_SECRET2_DIGEST_0                      (FUSE_CTRL_BASE_ADDR + 0xD8)
// #define FUSE_CTRL_SECRET2_DIGEST_1                      (FUSE_CTRL_BASE_ADDR + 0xDC)
// #define FUSE_CTRL_SW_CFG_WINDOW                         (FUSE_CTRL_BASE_ADDR + 0x1FC)


#define FUSE_CTRL_REGISTERS {   FUSE_CTRL_BASE_ADDR, \
								FUSE_CTRL_INTR_STATE, \
								FUSE_CTRL_INTR_ENABLE, \
								FUSE_CTRL_INTR_TEST, \
								FUSE_CTRL_ALERT_TEST, \
								FUSE_CTRL_STATUS, \
								FUSE_CTRL_ERR_CODE_0, \
								FUSE_CTRL_ERR_CODE_1, \
								FUSE_CTRL_ERR_CODE_2, \
								FUSE_CTRL_ERR_CODE_3, \
								FUSE_CTRL_ERR_CODE_4, \
								FUSE_CTRL_ERR_CODE_5, \
								FUSE_CTRL_ERR_CODE_6, \
								FUSE_CTRL_ERR_CODE_7, \
								FUSE_CTRL_ERR_CODE_8, \
								FUSE_CTRL_ERR_CODE_9, \
								FUSE_CTRL_ERR_CODE_10, \
								FUSE_CTRL_ERR_CODE_11, \
								FUSE_CTRL_ERR_CODE_12, \
								FUSE_CTRL_DIRECT_ACCESS_REGWEN, \
								FUSE_CTRL_DIRECT_ACCESS_CMD, \
								FUSE_CTRL_DIRECT_ACCESS_ADDRESS, \
								FUSE_CTRL_DIRECT_ACCESS_WDATA_0, \
								FUSE_CTRL_DIRECT_ACCESS_WDATA_1, \
								FUSE_CTRL_DIRECT_ACCESS_RDATA_0, \
								FUSE_CTRL_DIRECT_ACCESS_RDATA_1, \
								FUSE_CTRL_CHECK_TRIGGER_REGWEN, \
								FUSE_CTRL_CHECK_TRIGGER, \
								FUSE_CTRL_CHECK_REGWEN, \
								FUSE_CTRL_CHECK_TIMEOUT, \
								FUSE_CTRL_INTEGRITY_CHECK_PERIOD, \
								FUSE_CTRL_CONSISTENCY_CHECK_PERIOD, \
								FUSE_CTRL_VENDOR_TEST_READ_LOCK, \
								FUSE_CTRL_CREATOR_SW_CFG_READ_LOCK, \
								FUSE_CTRL_OWNER_SW_CFG_READ_LOCK, \
								FUSE_CTRL_ROT_CREATOR_AUTH_CODESIGN_READ_LOCK, \
								FUSE_CTRL_ROT_CREATOR_AUTH_STATE_READ_LOCK, \
								FUSE_CTRL_VENDOR_TEST_DIGEST_0, \
								FUSE_CTRL_VENDOR_TEST_DIGEST_1, \
								FUSE_CTRL_CREATOR_SW_CFG_DIGEST_0, \
								FUSE_CTRL_CREATOR_SW_CFG_DIGEST_1, \
								FUSE_CTRL_OWNER_SW_CFG_DIGEST_0, \
								FUSE_CTRL_OWNER_SW_CFG_DIGEST_1, \
								FUSE_CTRL_ROT_CREATOR_AUTH_CODESIGN_DIGEST_0, \
								FUSE_CTRL_ROT_CREATOR_AUTH_CODESIGN_DIGEST_1, \
								FUSE_CTRL_ROT_CREATOR_AUTH_STATE_DIGEST_0, \
								FUSE_CTRL_ROT_CREATOR_AUTH_STATE_DIGEST_1, \
								FUSE_CTRL_HW_CFG0_DIGEST_0, \
								FUSE_CTRL_HW_CFG0_DIGEST_1, \
								FUSE_CTRL_HW_CFG1_DIGEST_0, \
								FUSE_CTRL_HW_CFG1_DIGEST_1, \
								FUSE_CTRL_SECRET0_DIGEST_0, \
								FUSE_CTRL_SECRET0_DIGEST_1, \
								FUSE_CTRL_SECRET1_DIGEST_0, \
								FUSE_CTRL_SECRET1_DIGEST_1, \
								FUSE_CTRL_SECRET2_DIGEST_0, \
								FUSE_CTRL_SECRET2_DIGEST_1 }
//								FUSE_CTRL_SW_CFG_WINDOW         }
#endif
