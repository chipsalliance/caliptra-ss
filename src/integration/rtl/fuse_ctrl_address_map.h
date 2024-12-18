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

#define FUSE_CTRL_BASE_ADDR                             (0x50000000)
#define FUSE_CTRL_INTR_STATE                            (0x50000000)
#define FUSE_CTRL_INTR_ENABLE                           (0x50000004)
#define FUSE_CTRL_INTR_TEST                             (0x50000008)
#define FUSE_CTRL_ALERT_TEST                            (0x5000000C)
#define FUSE_CTRL_STATUS                                (0x50000010)
#define FUSE_CTRL_ERR_CODE_0                            (0x50000014)
#define FUSE_CTRL_ERR_CODE_1                            (0x50000018)
#define FUSE_CTRL_ERR_CODE_2                            (0x5000001C)
#define FUSE_CTRL_ERR_CODE_3                            (0x50000020)
#define FUSE_CTRL_ERR_CODE_4                            (0x50000024)
#define FUSE_CTRL_ERR_CODE_5                            (0x50000028)
#define FUSE_CTRL_ERR_CODE_6                            (0x5000002C)
#define FUSE_CTRL_ERR_CODE_7                            (0x50000030)
#define FUSE_CTRL_ERR_CODE_8                            (0x50000034)
#define FUSE_CTRL_ERR_CODE_9                            (0x50000038)
#define FUSE_CTRL_ERR_CODE_10                           (0x5000003C)
#define FUSE_CTRL_ERR_CODE_11                           (0x50000040)
#define FUSE_CTRL_ERR_CODE_12                           (0x50000044)
#define FUSE_CTRL_DIRECT_ACCESS_REGWEN                  (0x50000048)
#define FUSE_CTRL_DIRECT_ACCESS_CMD                     (0x5000004C)
#define FUSE_CTRL_DIRECT_ACCESS_ADDRESS                 (0x50000050)
#define FUSE_CTRL_DIRECT_ACCESS_WDATA_0                 (0x50000054)
#define FUSE_CTRL_DIRECT_ACCESS_WDATA_1                 (0x50000058)
#define FUSE_CTRL_DIRECT_ACCESS_RDATA_0                 (0x5000005C)
#define FUSE_CTRL_DIRECT_ACCESS_RDATA_1                 (0x50000060)
#define FUSE_CTRL_CHECK_TRIGGER_REGWEN                  (0x50000064)
#define FUSE_CTRL_CHECK_TRIGGER                         (0x50000068)
#define FUSE_CTRL_CHECK_REGWEN                          (0x5000006C)
#define FUSE_CTRL_CHECK_TIMEOUT                         (0x50000070)
#define FUSE_CTRL_INTEGRITY_CHECK_PERIOD                (0x50000074)
#define FUSE_CTRL_CONSISTENCY_CHECK_PERIOD              (0x50000078)
#define FUSE_CTRL_VENDOR_TEST_READ_LOCK                 (0x5000007C)
#define FUSE_CTRL_CREATOR_SW_CFG_READ_LOCK              (0x50000080)
#define FUSE_CTRL_OWNER_SW_CFG_READ_LOCK                (0x50000084)
#define FUSE_CTRL_ROT_CREATOR_AUTH_CODESIGN_READ_LOCK   (0x50000088)
#define FUSE_CTRL_ROT_CREATOR_AUTH_STATE_READ_LOCK      (0x5000008C)
#define FUSE_CTRL_VENDOR_TEST_DIGEST_0                  (0x50000090)
#define FUSE_CTRL_VENDOR_TEST_DIGEST_1                  (0x50000094)
#define FUSE_CTRL_CREATOR_SW_CFG_DIGEST_0               (0x50000098)
#define FUSE_CTRL_CREATOR_SW_CFG_DIGEST_1               (0x5000009C)
#define FUSE_CTRL_OWNER_SW_CFG_DIGEST_0                 (0x500000A0)
#define FUSE_CTRL_OWNER_SW_CFG_DIGEST_1                 (0x500000A4)
#define FUSE_CTRL_ROT_CREATOR_AUTH_CODESIGN_DIGEST_0    (0x500000A8)
#define FUSE_CTRL_ROT_CREATOR_AUTH_CODESIGN_DIGEST_1    (0x500000AC)
#define FUSE_CTRL_ROT_CREATOR_AUTH_STATE_DIGEST_0       (0x500000B0)
#define FUSE_CTRL_ROT_CREATOR_AUTH_STATE_DIGEST_1       (0x500000B4)
#define FUSE_CTRL_HW_CFG0_DIGEST_0                      (0x500000B8)
#define FUSE_CTRL_HW_CFG0_DIGEST_1                      (0x500000BC)
#define FUSE_CTRL_HW_CFG1_DIGEST_0                      (0x500000C0)
#define FUSE_CTRL_HW_CFG1_DIGEST_1                      (0x500000C4)
#define FUSE_CTRL_SECRET0_DIGEST_0                      (0x500000C8)
#define FUSE_CTRL_SECRET0_DIGEST_1                      (0x500000CC)
#define FUSE_CTRL_SECRET1_DIGEST_0                      (0x500000D0)
#define FUSE_CTRL_SECRET1_DIGEST_1                      (0x500000D4)
#define FUSE_CTRL_SECRET2_DIGEST_0                      (0x500000D8)
#define FUSE_CTRL_SECRET2_DIGEST_1                      (0x500000DC)
#define FUSE_CTRL_SW_CFG_WINDOW                         (0x50000800)

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
								FUSE_CTRL_SECRET2_DIGEST_1, \
								FUSE_CTRL_SW_CFG_WINDOW         }
#endif
