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
#ifndef MCI_REG_HEADER
#define MCI_REG_HEADER


#define MCI_REG_BASE_ADDR                                                                           (0x0)
#define MCI_REG_CAPABILITIES                                                                        (0x0)
#ifndef MCI_REG_CAPABILITIES
#define MCI_REG_CAPABILITIES                                                                        (0x0)
#define MCI_REG_CAPABILITIES_NUM_MBOX_LOW                                                           (0)
#define MCI_REG_CAPABILITIES_NUM_MBOX_MASK                                                          (0xf)
#endif
#define MCI_REG_HW_REV_ID                                                                           (0x4)
#ifndef MCI_REG_HW_REV_ID
#define MCI_REG_HW_REV_ID                                                                           (0x4)
#define MCI_REG_HW_REV_ID_MC_GENERATION_LOW                                                         (0)
#define MCI_REG_HW_REV_ID_MC_GENERATION_MASK                                                        (0xffff)
#define MCI_REG_HW_REV_ID_SOC_STEPPING_ID_LOW                                                       (16)
#define MCI_REG_HW_REV_ID_SOC_STEPPING_ID_MASK                                                      (0xffff0000)
#endif
#define MCI_REG_FW_REV_ID_0                                                                         (0x8)
#ifndef MCI_REG_FW_REV_ID_0
#define MCI_REG_FW_REV_ID_0                                                                         (0x8)
#endif
#define MCI_REG_FW_REV_ID_1                                                                         (0xc)
#ifndef MCI_REG_FW_REV_ID_1
#define MCI_REG_FW_REV_ID_1                                                                         (0xc)
#endif
#define MCI_REG_HW_CONFIG                                                                           (0x10)
#ifndef MCI_REG_HW_CONFIG
#define MCI_REG_HW_CONFIG                                                                           (0x10)
#define MCI_REG_HW_CONFIG_RSVD_EN_LOW                                                               (0)
#define MCI_REG_HW_CONFIG_RSVD_EN_MASK                                                              (0x1)
#endif
#define MCI_REG_FW_FLOW_STATUS                                                                      (0x20)
#ifndef MCI_REG_FW_FLOW_STATUS
#define MCI_REG_FW_FLOW_STATUS                                                                      (0x20)
#endif
#define MCI_REG_HW_FLOW_STATUS                                                                      (0x24)
#ifndef MCI_REG_HW_FLOW_STATUS
#define MCI_REG_HW_FLOW_STATUS                                                                      (0x24)
#define MCI_REG_HW_FLOW_STATUS_BOOT_FSM_LOW                                                         (0)
#define MCI_REG_HW_FLOW_STATUS_BOOT_FSM_MASK                                                        (0xf)
#endif
#define MCI_REG_RESET_REASON                                                                        (0x28)
#ifndef MCI_REG_RESET_REASON
#define MCI_REG_RESET_REASON                                                                        (0x28)
#define MCI_REG_RESET_REASON_FW_HITLESS_UPD_RESET_LOW                                               (0)
#define MCI_REG_RESET_REASON_FW_HITLESS_UPD_RESET_MASK                                              (0x1)
#define MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_LOW                                                  (1)
#define MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_MASK                                                 (0x2)
#define MCI_REG_RESET_REASON_WARM_RESET_LOW                                                         (2)
#define MCI_REG_RESET_REASON_WARM_RESET_MASK                                                        (0x4)
#endif
#define MCI_REG_RESET_STATUS                                                                        (0x2c)
#ifndef MCI_REG_RESET_STATUS
#define MCI_REG_RESET_STATUS                                                                        (0x2c)
#define MCI_REG_RESET_STATUS_CPTRA_RESET_STS_LOW                                                    (0)
#define MCI_REG_RESET_STATUS_CPTRA_RESET_STS_MASK                                                   (0x1)
#define MCI_REG_RESET_STATUS_MCU_RESET_STS_LOW                                                      (1)
#define MCI_REG_RESET_STATUS_MCU_RESET_STS_MASK                                                     (0x2)
#endif
#define MCI_REG_HW_ERROR_FATAL                                                                      (0x40)
#ifndef MCI_REG_HW_ERROR_FATAL
#define MCI_REG_HW_ERROR_FATAL                                                                      (0x40)
#define MCI_REG_HW_ERROR_FATAL_MCU_SRAM_ECC_UNC_LOW                                                 (0)
#define MCI_REG_HW_ERROR_FATAL_MCU_SRAM_ECC_UNC_MASK                                                (0x1)
#define MCI_REG_HW_ERROR_FATAL_NMI_PIN_LOW                                                          (1)
#define MCI_REG_HW_ERROR_FATAL_NMI_PIN_MASK                                                         (0x2)
#endif
#define MCI_REG_AGG_ERROR_FATAL                                                                     (0x44)
#ifndef MCI_REG_AGG_ERROR_FATAL
#define MCI_REG_AGG_ERROR_FATAL                                                                     (0x44)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL31_LOW                                               (0)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL31_MASK                                              (0x1)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL30_LOW                                               (1)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL30_MASK                                              (0x2)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL29_LOW                                               (2)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL29_MASK                                              (0x4)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL28_LOW                                               (3)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL28_MASK                                              (0x8)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL27_LOW                                               (4)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL27_MASK                                              (0x10)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL26_LOW                                               (5)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL26_MASK                                              (0x20)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL25_LOW                                               (6)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL25_MASK                                              (0x40)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL24_LOW                                               (7)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL24_MASK                                              (0x80)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL23_LOW                                               (8)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL23_MASK                                              (0x100)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL22_LOW                                               (9)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL22_MASK                                              (0x200)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL21_LOW                                               (10)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL21_MASK                                              (0x400)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL20_LOW                                               (11)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL20_MASK                                              (0x800)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL19_LOW                                               (12)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL19_MASK                                              (0x1000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL18_LOW                                               (13)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL18_MASK                                              (0x2000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL17_LOW                                               (14)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL17_MASK                                              (0x4000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL16_LOW                                               (15)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL16_MASK                                              (0x8000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL15_LOW                                               (16)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL15_MASK                                              (0x10000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL14_LOW                                               (17)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL14_MASK                                              (0x20000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL13_LOW                                               (18)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL13_MASK                                              (0x40000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL12_LOW                                               (19)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL12_MASK                                              (0x80000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL11_LOW                                               (20)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL11_MASK                                              (0x100000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL10_LOW                                               (21)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL10_MASK                                              (0x200000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL9_LOW                                                (22)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL9_MASK                                               (0x400000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL8_LOW                                                (23)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL8_MASK                                               (0x800000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL7_LOW                                                (24)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL7_MASK                                               (0x1000000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL6_LOW                                                (25)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL6_MASK                                               (0x2000000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL5_LOW                                                (26)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL5_MASK                                               (0x4000000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL4_LOW                                                (27)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL4_MASK                                               (0x8000000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL3_LOW                                                (28)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL3_MASK                                               (0x10000000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL2_LOW                                                (29)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL2_MASK                                               (0x20000000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL1_LOW                                                (30)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL1_MASK                                               (0x40000000)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL0_LOW                                                (31)
#define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL0_MASK                                               (0x80000000)
#endif
#define MCI_REG_HW_ERROR_NON_FATAL                                                                  (0x48)
#ifndef MCI_REG_HW_ERROR_NON_FATAL
#define MCI_REG_HW_ERROR_NON_FATAL                                                                  (0x48)
#define MCI_REG_HW_ERROR_NON_FATAL_RSVD_LOW                                                         (0)
#define MCI_REG_HW_ERROR_NON_FATAL_RSVD_MASK                                                        (0x1)
#endif
#define MCI_REG_AGG_ERROR_NON_FATAL                                                                 (0x4c)
#ifndef MCI_REG_AGG_ERROR_NON_FATAL
#define MCI_REG_AGG_ERROR_NON_FATAL                                                                 (0x4c)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL31_LOW                                       (0)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL31_MASK                                      (0x1)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL30_LOW                                       (1)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL30_MASK                                      (0x2)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL29_LOW                                       (2)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL29_MASK                                      (0x4)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL28_LOW                                       (3)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL28_MASK                                      (0x8)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL27_LOW                                       (4)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL27_MASK                                      (0x10)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL26_LOW                                       (5)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL26_MASK                                      (0x20)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL25_LOW                                       (6)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL25_MASK                                      (0x40)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL24_LOW                                       (7)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL24_MASK                                      (0x80)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL23_LOW                                       (8)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL23_MASK                                      (0x100)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL22_LOW                                       (9)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL22_MASK                                      (0x200)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL21_LOW                                       (10)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL21_MASK                                      (0x400)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL20_LOW                                       (11)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL20_MASK                                      (0x800)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL19_LOW                                       (12)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL19_MASK                                      (0x1000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL18_LOW                                       (13)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL18_MASK                                      (0x2000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL17_LOW                                       (14)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL17_MASK                                      (0x4000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL16_LOW                                       (15)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL16_MASK                                      (0x8000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL15_LOW                                       (16)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL15_MASK                                      (0x10000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL14_LOW                                       (17)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL14_MASK                                      (0x20000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL13_LOW                                       (18)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL13_MASK                                      (0x40000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL12_LOW                                       (19)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL12_MASK                                      (0x80000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL11_LOW                                       (20)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL11_MASK                                      (0x100000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL10_LOW                                       (21)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL10_MASK                                      (0x200000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL9_LOW                                        (22)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL9_MASK                                       (0x400000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL8_LOW                                        (23)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL8_MASK                                       (0x800000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL7_LOW                                        (24)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL7_MASK                                       (0x1000000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL6_LOW                                        (25)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL6_MASK                                       (0x2000000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL5_LOW                                        (26)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL5_MASK                                       (0x4000000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL4_LOW                                        (27)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL4_MASK                                       (0x8000000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL3_LOW                                        (28)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL3_MASK                                       (0x10000000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL2_LOW                                        (29)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL2_MASK                                       (0x20000000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL1_LOW                                        (30)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL1_MASK                                       (0x40000000)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL0_LOW                                        (31)
#define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL0_MASK                                       (0x80000000)
#endif
#define MCI_REG_FW_ERROR_FATAL                                                                      (0x50)
#ifndef MCI_REG_FW_ERROR_FATAL
#define MCI_REG_FW_ERROR_FATAL                                                                      (0x50)
#endif
#define MCI_REG_FW_ERROR_NON_FATAL                                                                  (0x54)
#ifndef MCI_REG_FW_ERROR_NON_FATAL
#define MCI_REG_FW_ERROR_NON_FATAL                                                                  (0x54)
#endif
#define MCI_REG_HW_ERROR_ENC                                                                        (0x58)
#ifndef MCI_REG_HW_ERROR_ENC
#define MCI_REG_HW_ERROR_ENC                                                                        (0x58)
#endif
#define MCI_REG_FW_ERROR_ENC                                                                        (0x5c)
#ifndef MCI_REG_FW_ERROR_ENC
#define MCI_REG_FW_ERROR_ENC                                                                        (0x5c)
#endif
#define MCI_REG_FW_EXTENDED_ERROR_INFO_0                                                            (0x60)
#ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_0
#define MCI_REG_FW_EXTENDED_ERROR_INFO_0                                                            (0x60)
#endif
#define MCI_REG_FW_EXTENDED_ERROR_INFO_1                                                            (0x64)
#ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_1
#define MCI_REG_FW_EXTENDED_ERROR_INFO_1                                                            (0x64)
#endif
#define MCI_REG_FW_EXTENDED_ERROR_INFO_2                                                            (0x68)
#ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_2
#define MCI_REG_FW_EXTENDED_ERROR_INFO_2                                                            (0x68)
#endif
#define MCI_REG_FW_EXTENDED_ERROR_INFO_3                                                            (0x6c)
#ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_3
#define MCI_REG_FW_EXTENDED_ERROR_INFO_3                                                            (0x6c)
#endif
#define MCI_REG_FW_EXTENDED_ERROR_INFO_4                                                            (0x70)
#ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_4
#define MCI_REG_FW_EXTENDED_ERROR_INFO_4                                                            (0x70)
#endif
#define MCI_REG_FW_EXTENDED_ERROR_INFO_5                                                            (0x74)
#ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_5
#define MCI_REG_FW_EXTENDED_ERROR_INFO_5                                                            (0x74)
#endif
#define MCI_REG_FW_EXTENDED_ERROR_INFO_6                                                            (0x78)
#ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_6
#define MCI_REG_FW_EXTENDED_ERROR_INFO_6                                                            (0x78)
#endif
#define MCI_REG_FW_EXTENDED_ERROR_INFO_7                                                            (0x7c)
#ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_7
#define MCI_REG_FW_EXTENDED_ERROR_INFO_7                                                            (0x7c)
#endif
#define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK                                                        (0x80)
#ifndef MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK
#define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK                                                        (0x80)
#define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_MCU_SRAM_ECC_UNC_LOW                              (0)
#define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_MCU_SRAM_ECC_UNC_MASK                             (0x1)
#define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_NMI_PIN_LOW                                       (1)
#define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_NMI_PIN_MASK                                      (0x2)
#endif
#define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK                                                    (0x84)
#ifndef MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK
#define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK                                                    (0x84)
#define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_FIXME_LOW                                          (0)
#define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_FIXME_MASK                                         (0x1)
#endif
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK                                                       (0x88)
#ifndef MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK                                                       (0x88)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL31_LOW                            (0)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL31_MASK                           (0x1)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL30_LOW                            (1)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL30_MASK                           (0x2)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL29_LOW                            (2)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL29_MASK                           (0x4)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL28_LOW                            (3)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL28_MASK                           (0x8)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL27_LOW                            (4)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL27_MASK                           (0x10)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL26_LOW                            (5)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL26_MASK                           (0x20)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL25_LOW                            (6)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL25_MASK                           (0x40)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL24_LOW                            (7)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL24_MASK                           (0x80)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL23_LOW                            (8)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL23_MASK                           (0x100)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL22_LOW                            (9)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL22_MASK                           (0x200)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL21_LOW                            (10)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL21_MASK                           (0x400)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL20_LOW                            (11)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL20_MASK                           (0x800)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL19_LOW                            (12)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL19_MASK                           (0x1000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL18_LOW                            (13)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL18_MASK                           (0x2000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL17_LOW                            (14)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL17_MASK                           (0x4000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL16_LOW                            (15)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL16_MASK                           (0x8000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL15_LOW                            (16)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL15_MASK                           (0x10000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL14_LOW                            (17)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL14_MASK                           (0x20000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL13_LOW                            (18)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL13_MASK                           (0x40000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL12_LOW                            (19)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL12_MASK                           (0x80000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL11_LOW                            (20)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL11_MASK                           (0x100000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL10_LOW                            (21)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL10_MASK                           (0x200000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL9_LOW                             (22)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL9_MASK                            (0x400000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL8_LOW                             (23)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL8_MASK                            (0x800000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL7_LOW                             (24)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL7_MASK                            (0x1000000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL6_LOW                             (25)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL6_MASK                            (0x2000000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL5_LOW                             (26)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL5_MASK                            (0x4000000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL4_LOW                             (27)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL4_MASK                            (0x8000000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL3_LOW                             (28)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL3_MASK                            (0x10000000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL2_LOW                             (29)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL2_MASK                            (0x20000000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL1_LOW                             (30)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL1_MASK                            (0x40000000)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL0_LOW                             (31)
#define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL0_MASK                            (0x80000000)
#endif
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK                                                   (0x8c)
#ifndef MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK                                                   (0x8c)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL31_LOW                    (0)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL31_MASK                   (0x1)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL30_LOW                    (1)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL30_MASK                   (0x2)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL29_LOW                    (2)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL29_MASK                   (0x4)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL28_LOW                    (3)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL28_MASK                   (0x8)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL27_LOW                    (4)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL27_MASK                   (0x10)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL26_LOW                    (5)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL26_MASK                   (0x20)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL25_LOW                    (6)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL25_MASK                   (0x40)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL24_LOW                    (7)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL24_MASK                   (0x80)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL23_LOW                    (8)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL23_MASK                   (0x100)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL22_LOW                    (9)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL22_MASK                   (0x200)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL21_LOW                    (10)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL21_MASK                   (0x400)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL20_LOW                    (11)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL20_MASK                   (0x800)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL19_LOW                    (12)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL19_MASK                   (0x1000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL18_LOW                    (13)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL18_MASK                   (0x2000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL17_LOW                    (14)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL17_MASK                   (0x4000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL16_LOW                    (15)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL16_MASK                   (0x8000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL15_LOW                    (16)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL15_MASK                   (0x10000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL14_LOW                    (17)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL14_MASK                   (0x20000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL13_LOW                    (18)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL13_MASK                   (0x40000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL12_LOW                    (19)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL12_MASK                   (0x80000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL11_LOW                    (20)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL11_MASK                   (0x100000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL10_LOW                    (21)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL10_MASK                   (0x200000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL9_LOW                     (22)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL9_MASK                    (0x400000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL8_LOW                     (23)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL8_MASK                    (0x800000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL7_LOW                     (24)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL7_MASK                    (0x1000000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL6_LOW                     (25)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL6_MASK                    (0x2000000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL5_LOW                     (26)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL5_MASK                    (0x4000000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL4_LOW                     (27)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL4_MASK                    (0x8000000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL3_LOW                     (28)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL3_MASK                    (0x10000000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL2_LOW                     (29)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL2_MASK                    (0x20000000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL1_LOW                     (30)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL1_MASK                    (0x40000000)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL0_LOW                     (31)
#define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL0_MASK                    (0x80000000)
#endif
#define MCI_REG_INTERNAL_FW_ERROR_FATAL_MASK                                                        (0x90)
#ifndef MCI_REG_INTERNAL_FW_ERROR_FATAL_MASK
#define MCI_REG_INTERNAL_FW_ERROR_FATAL_MASK                                                        (0x90)
#endif
#define MCI_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK                                                    (0x94)
#ifndef MCI_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK
#define MCI_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK                                                    (0x94)
#endif
#define MCI_REG_WDT_TIMER1_EN                                                                       (0xa0)
#ifndef MCI_REG_WDT_TIMER1_EN
#define MCI_REG_WDT_TIMER1_EN                                                                       (0xa0)
#define MCI_REG_WDT_TIMER1_EN_TIMER1_EN_LOW                                                         (0)
#define MCI_REG_WDT_TIMER1_EN_TIMER1_EN_MASK                                                        (0x1)
#endif
#define MCI_REG_WDT_TIMER1_CTRL                                                                     (0xa4)
#ifndef MCI_REG_WDT_TIMER1_CTRL
#define MCI_REG_WDT_TIMER1_CTRL                                                                     (0xa4)
#define MCI_REG_WDT_TIMER1_CTRL_TIMER1_RESTART_LOW                                                  (0)
#define MCI_REG_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK                                                 (0x1)
#endif
#define MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_0                                                         (0xa8)
#ifndef MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_0
#define MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_0                                                         (0xa8)
#endif
#define MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_1                                                         (0xac)
#ifndef MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_1
#define MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_1                                                         (0xac)
#endif
#define MCI_REG_WDT_TIMER2_EN                                                                       (0xb0)
#ifndef MCI_REG_WDT_TIMER2_EN
#define MCI_REG_WDT_TIMER2_EN                                                                       (0xb0)
#define MCI_REG_WDT_TIMER2_EN_TIMER2_EN_LOW                                                         (0)
#define MCI_REG_WDT_TIMER2_EN_TIMER2_EN_MASK                                                        (0x1)
#endif
#define MCI_REG_WDT_TIMER2_CTRL                                                                     (0xb4)
#ifndef MCI_REG_WDT_TIMER2_CTRL
#define MCI_REG_WDT_TIMER2_CTRL                                                                     (0xb4)
#define MCI_REG_WDT_TIMER2_CTRL_TIMER2_RESTART_LOW                                                  (0)
#define MCI_REG_WDT_TIMER2_CTRL_TIMER2_RESTART_MASK                                                 (0x1)
#endif
#define MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_0                                                         (0xb8)
#ifndef MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_0
#define MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_0                                                         (0xb8)
#endif
#define MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_1                                                         (0xbc)
#ifndef MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_1
#define MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_1                                                         (0xbc)
#endif
#define MCI_REG_WDT_STATUS                                                                          (0xc0)
#ifndef MCI_REG_WDT_STATUS
#define MCI_REG_WDT_STATUS                                                                          (0xc0)
#define MCI_REG_WDT_STATUS_T1_TIMEOUT_LOW                                                           (0)
#define MCI_REG_WDT_STATUS_T1_TIMEOUT_MASK                                                          (0x1)
#define MCI_REG_WDT_STATUS_T2_TIMEOUT_LOW                                                           (1)
#define MCI_REG_WDT_STATUS_T2_TIMEOUT_MASK                                                          (0x2)
#endif
#define MCI_REG_WDT_CFG_0                                                                           (0xd0)
#ifndef MCI_REG_WDT_CFG_0
#define MCI_REG_WDT_CFG_0                                                                           (0xd0)
#endif
#define MCI_REG_WDT_CFG_1                                                                           (0xd4)
#ifndef MCI_REG_WDT_CFG_1
#define MCI_REG_WDT_CFG_1                                                                           (0xd4)
#endif
#define MCI_REG_MCU_TIMER_CONFIG                                                                    (0xe0)
#ifndef MCI_REG_MCU_TIMER_CONFIG
#define MCI_REG_MCU_TIMER_CONFIG                                                                    (0xe0)
#endif
#define MCI_REG_MCU_RV_MTIME_L                                                                      (0xe4)
#ifndef MCI_REG_MCU_RV_MTIME_L
#define MCI_REG_MCU_RV_MTIME_L                                                                      (0xe4)
#endif
#define MCI_REG_MCU_RV_MTIME_H                                                                      (0xe8)
#ifndef MCI_REG_MCU_RV_MTIME_H
#define MCI_REG_MCU_RV_MTIME_H                                                                      (0xe8)
#endif
#define MCI_REG_MCU_RV_MTIMECMP_L                                                                   (0xec)
#ifndef MCI_REG_MCU_RV_MTIMECMP_L
#define MCI_REG_MCU_RV_MTIMECMP_L                                                                   (0xec)
#endif
#define MCI_REG_MCU_RV_MTIMECMP_H                                                                   (0xf0)
#ifndef MCI_REG_MCU_RV_MTIMECMP_H
#define MCI_REG_MCU_RV_MTIMECMP_H                                                                   (0xf0)
#endif
#define MCI_REG_RESET_REQUEST                                                                       (0x100)
#ifndef MCI_REG_RESET_REQUEST
#define MCI_REG_RESET_REQUEST                                                                       (0x100)
#define MCI_REG_RESET_REQUEST_MCU_REQ_LOW                                                           (0)
#define MCI_REG_RESET_REQUEST_MCU_REQ_MASK                                                          (0x1)
#endif
#define MCI_REG_MCI_BOOTFSM_GO                                                                      (0x104)
#ifndef MCI_REG_MCI_BOOTFSM_GO
#define MCI_REG_MCI_BOOTFSM_GO                                                                      (0x104)
#define MCI_REG_MCI_BOOTFSM_GO_GO_LOW                                                               (0)
#define MCI_REG_MCI_BOOTFSM_GO_GO_MASK                                                              (0x1)
#endif
#define MCI_REG_FW_SRAM_EXEC_REGION_SIZE                                                            (0x108)
#ifndef MCI_REG_FW_SRAM_EXEC_REGION_SIZE
#define MCI_REG_FW_SRAM_EXEC_REGION_SIZE                                                            (0x108)
#define MCI_REG_FW_SRAM_EXEC_REGION_SIZE_SIZE_LOW                                                   (0)
#define MCI_REG_FW_SRAM_EXEC_REGION_SIZE_SIZE_MASK                                                  (0xffff)
#endif
#define MCI_REG_MCU_NMI_VECTOR                                                                      (0x10c)
#ifndef MCI_REG_MCU_NMI_VECTOR
#define MCI_REG_MCU_NMI_VECTOR                                                                      (0x10c)
#endif
#define MCI_REG_MCU_RESET_VECTOR                                                                    (0x110)
#ifndef MCI_REG_MCU_RESET_VECTOR
#define MCI_REG_MCU_RESET_VECTOR                                                                    (0x110)
#endif
#define MCI_REG_MBOX0_VALID_AXI_ID_0                                                                (0x180)
#ifndef MCI_REG_MBOX0_VALID_AXI_ID_0
#define MCI_REG_MBOX0_VALID_AXI_ID_0                                                                (0x180)
#endif
#define MCI_REG_MBOX0_VALID_AXI_ID_1                                                                (0x184)
#ifndef MCI_REG_MBOX0_VALID_AXI_ID_1
#define MCI_REG_MBOX0_VALID_AXI_ID_1                                                                (0x184)
#endif
#define MCI_REG_MBOX0_VALID_AXI_ID_2                                                                (0x188)
#ifndef MCI_REG_MBOX0_VALID_AXI_ID_2
#define MCI_REG_MBOX0_VALID_AXI_ID_2                                                                (0x188)
#endif
#define MCI_REG_MBOX0_VALID_AXI_ID_3                                                                (0x18c)
#ifndef MCI_REG_MBOX0_VALID_AXI_ID_3
#define MCI_REG_MBOX0_VALID_AXI_ID_3                                                                (0x18c)
#endif
#define MCI_REG_MBOX0_VALID_AXI_ID_4                                                                (0x190)
#ifndef MCI_REG_MBOX0_VALID_AXI_ID_4
#define MCI_REG_MBOX0_VALID_AXI_ID_4                                                                (0x190)
#endif
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_0                                                           (0x1a0)
#ifndef MCI_REG_MBOX0_VALID_AXI_ID_LOCK_0
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_0                                                           (0x1a0)
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_0_LOCK_LOW                                                  (0)
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_0_LOCK_MASK                                                 (0x1)
#endif
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_1                                                           (0x1a4)
#ifndef MCI_REG_MBOX0_VALID_AXI_ID_LOCK_1
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_1                                                           (0x1a4)
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_1_LOCK_LOW                                                  (0)
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_1_LOCK_MASK                                                 (0x1)
#endif
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_2                                                           (0x1a8)
#ifndef MCI_REG_MBOX0_VALID_AXI_ID_LOCK_2
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_2                                                           (0x1a8)
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_2_LOCK_LOW                                                  (0)
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_2_LOCK_MASK                                                 (0x1)
#endif
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_3                                                           (0x1ac)
#ifndef MCI_REG_MBOX0_VALID_AXI_ID_LOCK_3
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_3                                                           (0x1ac)
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_3_LOCK_LOW                                                  (0)
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_3_LOCK_MASK                                                 (0x1)
#endif
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_4                                                           (0x1b0)
#ifndef MCI_REG_MBOX0_VALID_AXI_ID_LOCK_4
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_4                                                           (0x1b0)
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_4_LOCK_LOW                                                  (0)
#define MCI_REG_MBOX0_VALID_AXI_ID_LOCK_4_LOCK_MASK                                                 (0x1)
#endif
#define MCI_REG_MBOX1_VALID_AXI_ID_0                                                                (0x1c0)
#ifndef MCI_REG_MBOX1_VALID_AXI_ID_0
#define MCI_REG_MBOX1_VALID_AXI_ID_0                                                                (0x1c0)
#endif
#define MCI_REG_MBOX1_VALID_AXI_ID_1                                                                (0x1c4)
#ifndef MCI_REG_MBOX1_VALID_AXI_ID_1
#define MCI_REG_MBOX1_VALID_AXI_ID_1                                                                (0x1c4)
#endif
#define MCI_REG_MBOX1_VALID_AXI_ID_2                                                                (0x1c8)
#ifndef MCI_REG_MBOX1_VALID_AXI_ID_2
#define MCI_REG_MBOX1_VALID_AXI_ID_2                                                                (0x1c8)
#endif
#define MCI_REG_MBOX1_VALID_AXI_ID_3                                                                (0x1cc)
#ifndef MCI_REG_MBOX1_VALID_AXI_ID_3
#define MCI_REG_MBOX1_VALID_AXI_ID_3                                                                (0x1cc)
#endif
#define MCI_REG_MBOX1_VALID_AXI_ID_4                                                                (0x1d0)
#ifndef MCI_REG_MBOX1_VALID_AXI_ID_4
#define MCI_REG_MBOX1_VALID_AXI_ID_4                                                                (0x1d0)
#endif
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_0                                                           (0x1e0)
#ifndef MCI_REG_MBOX1_VALID_AXI_ID_LOCK_0
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_0                                                           (0x1e0)
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_0_LOCK_LOW                                                  (0)
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_0_LOCK_MASK                                                 (0x1)
#endif
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_1                                                           (0x1e4)
#ifndef MCI_REG_MBOX1_VALID_AXI_ID_LOCK_1
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_1                                                           (0x1e4)
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_1_LOCK_LOW                                                  (0)
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_1_LOCK_MASK                                                 (0x1)
#endif
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_2                                                           (0x1e8)
#ifndef MCI_REG_MBOX1_VALID_AXI_ID_LOCK_2
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_2                                                           (0x1e8)
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_2_LOCK_LOW                                                  (0)
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_2_LOCK_MASK                                                 (0x1)
#endif
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_3                                                           (0x1ec)
#ifndef MCI_REG_MBOX1_VALID_AXI_ID_LOCK_3
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_3                                                           (0x1ec)
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_3_LOCK_LOW                                                  (0)
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_3_LOCK_MASK                                                 (0x1)
#endif
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_4                                                           (0x1f0)
#ifndef MCI_REG_MBOX1_VALID_AXI_ID_LOCK_4
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_4                                                           (0x1f0)
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_4_LOCK_LOW                                                  (0)
#define MCI_REG_MBOX1_VALID_AXI_ID_LOCK_4_LOCK_MASK                                                 (0x1)
#endif
#define MCI_REG_GENERIC_INPUT_WIRES_0                                                               (0x400)
#ifndef MCI_REG_GENERIC_INPUT_WIRES_0
#define MCI_REG_GENERIC_INPUT_WIRES_0                                                               (0x400)
#endif
#define MCI_REG_GENERIC_INPUT_WIRES_1                                                               (0x404)
#ifndef MCI_REG_GENERIC_INPUT_WIRES_1
#define MCI_REG_GENERIC_INPUT_WIRES_1                                                               (0x404)
#endif
#define MCI_REG_GENERIC_OUTPUT_WIRES_0                                                              (0x408)
#ifndef MCI_REG_GENERIC_OUTPUT_WIRES_0
#define MCI_REG_GENERIC_OUTPUT_WIRES_0                                                              (0x408)
#endif
#define MCI_REG_GENERIC_OUTPUT_WIRES_1                                                              (0x40c)
#ifndef MCI_REG_GENERIC_OUTPUT_WIRES_1
#define MCI_REG_GENERIC_OUTPUT_WIRES_1                                                              (0x40c)
#endif
#define MCI_REG_DEBUG_IN                                                                            (0x410)
#ifndef MCI_REG_DEBUG_IN
#define MCI_REG_DEBUG_IN                                                                            (0x410)
#define MCI_REG_DEBUG_IN_FIXME_LOW                                                                  (0)
#define MCI_REG_DEBUG_IN_FIXME_MASK                                                                 (0x1)
#endif
#define MCI_REG_DEBUG_OUT                                                                           (0x414)
#ifndef MCI_REG_DEBUG_OUT
#define MCI_REG_DEBUG_OUT                                                                           (0x414)
#define MCI_REG_DEBUG_OUT_FIXME_LOW                                                                 (0)
#define MCI_REG_DEBUG_OUT_FIXME_MASK                                                                (0x1)
#endif
#define MCI_REG_SS_DEBUG_INTENT                                                                     (0x418)
#ifndef MCI_REG_SS_DEBUG_INTENT
#define MCI_REG_SS_DEBUG_INTENT                                                                     (0x418)
#define MCI_REG_SS_DEBUG_INTENT_DEBUG_INTENT_LOW                                                    (0)
#define MCI_REG_SS_DEBUG_INTENT_DEBUG_INTENT_MASK                                                   (0x1)
#endif
#define MCI_REG_SS_CONFIG_DONE                                                                      (0x440)
#ifndef MCI_REG_SS_CONFIG_DONE
#define MCI_REG_SS_CONFIG_DONE                                                                      (0x440)
#define MCI_REG_SS_CONFIG_DONE_DONE_LOW                                                             (0)
#define MCI_REG_SS_CONFIG_DONE_DONE_MASK                                                            (0x1)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_0                                                   (0x480)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_0
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_0                                                   (0x480)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_1                                                   (0x484)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_1
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_1                                                   (0x484)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_2                                                   (0x488)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_2
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_2                                                   (0x488)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_3                                                   (0x48c)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_3
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_3                                                   (0x48c)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_4                                                   (0x490)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_4
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_4                                                   (0x490)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_5                                                   (0x494)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_5
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_5                                                   (0x494)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_6                                                   (0x498)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_6
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_6                                                   (0x498)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_7                                                   (0x49c)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_7
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_7                                                   (0x49c)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_8                                                   (0x4a0)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_8
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_8                                                   (0x4a0)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_9                                                   (0x4a4)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_9
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_9                                                   (0x4a4)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_10                                                  (0x4a8)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_10
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_10                                                  (0x4a8)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_11                                                  (0x4ac)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_11
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_11                                                  (0x4ac)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_0                                                   (0x4b0)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_0
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_0                                                   (0x4b0)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_1                                                   (0x4b4)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_1
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_1                                                   (0x4b4)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_2                                                   (0x4b8)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_2
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_2                                                   (0x4b8)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_3                                                   (0x4bc)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_3
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_3                                                   (0x4bc)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_4                                                   (0x4c0)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_4
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_4                                                   (0x4c0)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_5                                                   (0x4c4)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_5
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_5                                                   (0x4c4)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_6                                                   (0x4c8)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_6
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_6                                                   (0x4c8)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_7                                                   (0x4cc)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_7
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_7                                                   (0x4cc)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_8                                                   (0x4d0)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_8
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_8                                                   (0x4d0)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_9                                                   (0x4d4)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_9
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_9                                                   (0x4d4)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_10                                                  (0x4d8)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_10
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_10                                                  (0x4d8)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_11                                                  (0x4dc)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_11
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_11                                                  (0x4dc)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_0                                                   (0x4e0)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_0
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_0                                                   (0x4e0)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_1                                                   (0x4e4)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_1
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_1                                                   (0x4e4)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_2                                                   (0x4e8)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_2
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_2                                                   (0x4e8)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_3                                                   (0x4ec)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_3
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_3                                                   (0x4ec)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_4                                                   (0x4f0)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_4
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_4                                                   (0x4f0)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_5                                                   (0x4f4)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_5
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_5                                                   (0x4f4)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_6                                                   (0x4f8)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_6
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_6                                                   (0x4f8)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_7                                                   (0x4fc)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_7
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_7                                                   (0x4fc)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_8                                                   (0x500)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_8
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_8                                                   (0x500)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_9                                                   (0x504)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_9
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_9                                                   (0x504)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_10                                                  (0x508)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_10
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_10                                                  (0x508)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_11                                                  (0x50c)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_11
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_11                                                  (0x50c)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_0                                                   (0x510)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_0
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_0                                                   (0x510)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_1                                                   (0x514)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_1
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_1                                                   (0x514)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_2                                                   (0x518)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_2
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_2                                                   (0x518)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_3                                                   (0x51c)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_3
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_3                                                   (0x51c)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_4                                                   (0x520)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_4
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_4                                                   (0x520)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_5                                                   (0x524)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_5
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_5                                                   (0x524)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_6                                                   (0x528)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_6
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_6                                                   (0x528)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_7                                                   (0x52c)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_7
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_7                                                   (0x52c)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_8                                                   (0x530)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_8
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_8                                                   (0x530)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_9                                                   (0x534)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_9
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_9                                                   (0x534)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_10                                                  (0x538)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_10
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_10                                                  (0x538)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_11                                                  (0x53c)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_11
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_11                                                  (0x53c)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_0                                                   (0x540)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_0
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_0                                                   (0x540)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_1                                                   (0x544)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_1
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_1                                                   (0x544)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_2                                                   (0x548)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_2
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_2                                                   (0x548)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_3                                                   (0x54c)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_3
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_3                                                   (0x54c)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_4                                                   (0x550)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_4
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_4                                                   (0x550)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_5                                                   (0x554)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_5
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_5                                                   (0x554)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_6                                                   (0x558)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_6
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_6                                                   (0x558)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_7                                                   (0x55c)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_7
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_7                                                   (0x55c)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_8                                                   (0x560)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_8
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_8                                                   (0x560)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_9                                                   (0x564)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_9
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_9                                                   (0x564)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_10                                                  (0x568)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_10
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_10                                                  (0x568)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_11                                                  (0x56c)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_11
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_11                                                  (0x56c)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_0                                                   (0x570)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_0
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_0                                                   (0x570)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_1                                                   (0x574)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_1
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_1                                                   (0x574)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_2                                                   (0x578)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_2
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_2                                                   (0x578)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_3                                                   (0x57c)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_3
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_3                                                   (0x57c)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_4                                                   (0x580)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_4
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_4                                                   (0x580)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_5                                                   (0x584)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_5
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_5                                                   (0x584)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_6                                                   (0x588)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_6
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_6                                                   (0x588)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_7                                                   (0x58c)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_7
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_7                                                   (0x58c)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_8                                                   (0x590)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_8
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_8                                                   (0x590)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_9                                                   (0x594)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_9
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_9                                                   (0x594)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_10                                                  (0x598)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_10
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_10                                                  (0x598)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_11                                                  (0x59c)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_11
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_11                                                  (0x59c)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_0                                                   (0x5a0)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_0
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_0                                                   (0x5a0)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_1                                                   (0x5a4)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_1
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_1                                                   (0x5a4)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_2                                                   (0x5a8)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_2
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_2                                                   (0x5a8)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_3                                                   (0x5ac)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_3
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_3                                                   (0x5ac)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_4                                                   (0x5b0)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_4
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_4                                                   (0x5b0)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_5                                                   (0x5b4)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_5
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_5                                                   (0x5b4)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_6                                                   (0x5b8)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_6
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_6                                                   (0x5b8)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_7                                                   (0x5bc)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_7
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_7                                                   (0x5bc)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_8                                                   (0x5c0)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_8
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_8                                                   (0x5c0)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_9                                                   (0x5c4)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_9
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_9                                                   (0x5c4)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_10                                                  (0x5c8)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_10
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_10                                                  (0x5c8)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_11                                                  (0x5cc)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_11
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_11                                                  (0x5cc)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_0                                                   (0x5d0)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_0
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_0                                                   (0x5d0)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_1                                                   (0x5d4)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_1
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_1                                                   (0x5d4)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_2                                                   (0x5d8)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_2
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_2                                                   (0x5d8)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_3                                                   (0x5dc)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_3
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_3                                                   (0x5dc)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_4                                                   (0x5e0)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_4
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_4                                                   (0x5e0)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_5                                                   (0x5e4)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_5
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_5                                                   (0x5e4)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_6                                                   (0x5e8)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_6
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_6                                                   (0x5e8)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_7                                                   (0x5ec)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_7
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_7                                                   (0x5ec)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_8                                                   (0x5f0)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_8
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_8                                                   (0x5f0)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_9                                                   (0x5f4)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_9
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_9                                                   (0x5f4)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_10                                                  (0x5f8)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_10
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_10                                                  (0x5f8)
#endif
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_11                                                  (0x5fc)
#ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_11
#define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_11                                                  (0x5fc)
#endif
#define MCI_REG_INTR_BLOCK_RF_START                                                                 (0x1000)
#define MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                      (0x1000)
#ifndef MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
#define MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                      (0x1000)
#define MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                         (0)
#define MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                        (0x1)
#define MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                         (1)
#define MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                        (0x2)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R                                                      (0x1004)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R                                                      (0x1004)
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_LOW                      (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_MASK                     (0x1)
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_LOW                      (1)
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_MASK                     (0x2)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R                                                      (0x1008)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R                                                      (0x1008)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL31_EN_LOW                       (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL31_EN_MASK                      (0x1)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL30_EN_LOW                       (1)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL30_EN_MASK                      (0x2)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL29_EN_LOW                       (2)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL29_EN_MASK                      (0x4)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL28_EN_LOW                       (3)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL28_EN_MASK                      (0x8)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL27_EN_LOW                       (4)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL27_EN_MASK                      (0x10)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL26_EN_LOW                       (5)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL26_EN_MASK                      (0x20)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL25_EN_LOW                       (6)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL25_EN_MASK                      (0x40)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL24_EN_LOW                       (7)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL24_EN_MASK                      (0x80)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL23_EN_LOW                       (8)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL23_EN_MASK                      (0x100)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL22_EN_LOW                       (9)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL22_EN_MASK                      (0x200)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL21_EN_LOW                       (10)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL21_EN_MASK                      (0x400)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL20_EN_LOW                       (11)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL20_EN_MASK                      (0x800)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL19_EN_LOW                       (12)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL19_EN_MASK                      (0x1000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL18_EN_LOW                       (13)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL18_EN_MASK                      (0x2000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL17_EN_LOW                       (14)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL17_EN_MASK                      (0x4000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL16_EN_LOW                       (15)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL16_EN_MASK                      (0x8000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL15_EN_LOW                       (16)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL15_EN_MASK                      (0x10000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL14_EN_LOW                       (17)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL14_EN_MASK                      (0x20000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL13_EN_LOW                       (18)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL13_EN_MASK                      (0x40000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL12_EN_LOW                       (19)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL12_EN_MASK                      (0x80000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL11_EN_LOW                       (20)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL11_EN_MASK                      (0x100000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL10_EN_LOW                       (21)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL10_EN_MASK                      (0x200000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL9_EN_LOW                        (22)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL9_EN_MASK                       (0x400000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL8_EN_LOW                        (23)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL8_EN_MASK                       (0x800000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL7_EN_LOW                        (24)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL7_EN_MASK                       (0x1000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL6_EN_LOW                        (25)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL6_EN_MASK                       (0x2000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL5_EN_LOW                        (26)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL5_EN_MASK                       (0x4000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL4_EN_LOW                        (27)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL4_EN_MASK                       (0x8000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL3_EN_LOW                        (28)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL3_EN_MASK                       (0x10000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL2_EN_LOW                        (29)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL2_EN_MASK                       (0x20000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL1_EN_LOW                        (30)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL1_EN_MASK                       (0x40000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL0_EN_LOW                        (31)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL0_EN_MASK                       (0x80000000)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R                                                      (0x100c)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R                                                      (0x100c)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MCU_SRAM_ECC_COR_EN_LOW                        (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MCU_SRAM_ECC_COR_EN_MASK                       (0x1)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_CLPRA_MCU_RESET_REQ_EN_LOW                     (1)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_CLPRA_MCU_RESET_REQ_EN_MASK                    (0x2)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_GEN_IN_TOGGLE_EN_LOW                           (2)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_GEN_IN_TOGGLE_EN_MASK                          (0x4)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R                                                      (0x1010)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R                                                      (0x1010)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL31_EN_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL31_EN_MASK                  (0x1)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL30_EN_LOW                   (1)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL30_EN_MASK                  (0x2)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL29_EN_LOW                   (2)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL29_EN_MASK                  (0x4)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL28_EN_LOW                   (3)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL28_EN_MASK                  (0x8)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL27_EN_LOW                   (4)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL27_EN_MASK                  (0x10)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL26_EN_LOW                   (5)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL26_EN_MASK                  (0x20)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL25_EN_LOW                   (6)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL25_EN_MASK                  (0x40)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL24_EN_LOW                   (7)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL24_EN_MASK                  (0x80)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL23_EN_LOW                   (8)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL23_EN_MASK                  (0x100)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL22_EN_LOW                   (9)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL22_EN_MASK                  (0x200)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL21_EN_LOW                   (10)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL21_EN_MASK                  (0x400)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL20_EN_LOW                   (11)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL20_EN_MASK                  (0x800)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL19_EN_LOW                   (12)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL19_EN_MASK                  (0x1000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL18_EN_LOW                   (13)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL18_EN_MASK                  (0x2000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL17_EN_LOW                   (14)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL17_EN_MASK                  (0x4000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL16_EN_LOW                   (15)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL16_EN_MASK                  (0x8000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL15_EN_LOW                   (16)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL15_EN_MASK                  (0x10000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL14_EN_LOW                   (17)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL14_EN_MASK                  (0x20000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL13_EN_LOW                   (18)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL13_EN_MASK                  (0x40000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL12_EN_LOW                   (19)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL12_EN_MASK                  (0x80000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL11_EN_LOW                   (20)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL11_EN_MASK                  (0x100000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL10_EN_LOW                   (21)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL10_EN_MASK                  (0x200000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL9_EN_LOW                    (22)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL9_EN_MASK                   (0x400000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL8_EN_LOW                    (23)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL8_EN_MASK                   (0x800000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL7_EN_LOW                    (24)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL7_EN_MASK                   (0x1000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL6_EN_LOW                    (25)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL6_EN_MASK                   (0x2000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL5_EN_LOW                    (26)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL5_EN_MASK                   (0x4000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL4_EN_LOW                    (27)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL4_EN_MASK                   (0x8000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL3_EN_LOW                    (28)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL3_EN_MASK                   (0x10000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL2_EN_LOW                    (29)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL2_EN_MASK                   (0x20000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL1_EN_LOW                    (30)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL1_EN_MASK                   (0x40000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL0_EN_LOW                    (31)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL0_EN_MASK                   (0x80000000)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                                   (0x1014)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                                   (0x1014)
#define MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS0_LOW                                      (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS0_MASK                                     (0x1)
#define MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS1_LOW                                      (1)
#define MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS1_MASK                                     (0x2)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                                   (0x1018)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                                   (0x1018)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS0_LOW                                      (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS0_MASK                                     (0x1)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS1_LOW                                      (1)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS1_MASK                                     (0x2)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R                                                (0x101c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R                                                (0x101c)
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK              (0x1)
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_LOW               (1)
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_MASK              (0x2)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R                                                (0x1020)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R                                                (0x1020)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL31_STS_LOW                (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL31_STS_MASK               (0x1)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL30_STS_LOW                (1)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL30_STS_MASK               (0x2)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL29_STS_LOW                (2)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL29_STS_MASK               (0x4)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL28_STS_LOW                (3)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL28_STS_MASK               (0x8)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL27_STS_LOW                (4)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL27_STS_MASK               (0x10)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL26_STS_LOW                (5)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL26_STS_MASK               (0x20)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL25_STS_LOW                (6)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL25_STS_MASK               (0x40)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL24_STS_LOW                (7)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL24_STS_MASK               (0x80)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL23_STS_LOW                (8)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL23_STS_MASK               (0x100)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL22_STS_LOW                (9)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL22_STS_MASK               (0x200)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL21_STS_LOW                (10)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL21_STS_MASK               (0x400)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL20_STS_LOW                (11)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL20_STS_MASK               (0x800)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL19_STS_LOW                (12)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL19_STS_MASK               (0x1000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL18_STS_LOW                (13)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL18_STS_MASK               (0x2000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL17_STS_LOW                (14)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL17_STS_MASK               (0x4000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL16_STS_LOW                (15)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL16_STS_MASK               (0x8000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL15_STS_LOW                (16)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL15_STS_MASK               (0x10000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL14_STS_LOW                (17)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL14_STS_MASK               (0x20000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL13_STS_LOW                (18)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL13_STS_MASK               (0x40000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL12_STS_LOW                (19)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL12_STS_MASK               (0x80000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL11_STS_LOW                (20)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL11_STS_MASK               (0x100000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL10_STS_LOW                (21)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL10_STS_MASK               (0x200000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL9_STS_LOW                 (22)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL9_STS_MASK                (0x400000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL8_STS_LOW                 (23)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL8_STS_MASK                (0x800000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL7_STS_LOW                 (24)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL7_STS_MASK                (0x1000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL6_STS_LOW                 (25)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL6_STS_MASK                (0x2000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL5_STS_LOW                 (26)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL5_STS_MASK                (0x4000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL4_STS_LOW                 (27)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL4_STS_MASK                (0x8000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL3_STS_LOW                 (28)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL3_STS_MASK                (0x10000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL2_STS_LOW                 (29)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL2_STS_MASK                (0x20000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL1_STS_LOW                 (30)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL1_STS_MASK                (0x40000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL0_STS_LOW                 (31)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL0_STS_MASK                (0x80000000)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R                                                (0x1024)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R                                                (0x1024)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MCU_SRAM_ECC_COR_STS_LOW                 (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MCU_SRAM_ECC_COR_STS_MASK                (0x1)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CLPRA_MCU_RESET_REQ_STS_LOW              (1)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CLPRA_MCU_RESET_REQ_STS_MASK             (0x2)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_LOW                    (2)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK                   (0x4)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R                                                (0x1028)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R                                                (0x1028)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL31_STS_LOW            (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL31_STS_MASK           (0x1)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL30_STS_LOW            (1)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL30_STS_MASK           (0x2)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL29_STS_LOW            (2)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL29_STS_MASK           (0x4)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL28_STS_LOW            (3)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL28_STS_MASK           (0x8)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL27_STS_LOW            (4)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL27_STS_MASK           (0x10)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL26_STS_LOW            (5)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL26_STS_MASK           (0x20)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL25_STS_LOW            (6)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL25_STS_MASK           (0x40)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL24_STS_LOW            (7)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL24_STS_MASK           (0x80)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL23_STS_LOW            (8)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL23_STS_MASK           (0x100)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL22_STS_LOW            (9)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL22_STS_MASK           (0x200)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL21_STS_LOW            (10)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL21_STS_MASK           (0x400)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL20_STS_LOW            (11)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL20_STS_MASK           (0x800)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL19_STS_LOW            (12)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL19_STS_MASK           (0x1000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL18_STS_LOW            (13)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL18_STS_MASK           (0x2000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL17_STS_LOW            (14)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL17_STS_MASK           (0x4000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL16_STS_LOW            (15)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL16_STS_MASK           (0x8000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL15_STS_LOW            (16)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL15_STS_MASK           (0x10000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL14_STS_LOW            (17)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL14_STS_MASK           (0x20000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL13_STS_LOW            (18)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL13_STS_MASK           (0x40000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL12_STS_LOW            (19)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL12_STS_MASK           (0x80000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL11_STS_LOW            (20)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL11_STS_MASK           (0x100000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL10_STS_LOW            (21)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL10_STS_MASK           (0x200000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL9_STS_LOW             (22)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL9_STS_MASK            (0x400000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL8_STS_LOW             (23)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL8_STS_MASK            (0x800000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL7_STS_LOW             (24)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL7_STS_MASK            (0x1000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL6_STS_LOW             (25)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL6_STS_MASK            (0x2000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL5_STS_LOW             (26)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL5_STS_MASK            (0x4000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL4_STS_LOW             (27)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL4_STS_MASK            (0x8000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL3_STS_LOW             (28)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL3_STS_MASK            (0x10000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL2_STS_LOW             (29)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL2_STS_MASK            (0x20000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL1_STS_LOW             (30)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL1_STS_MASK            (0x40000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL0_STS_LOW             (31)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL0_STS_MASK            (0x80000000)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R                                                    (0x102c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R                                                    (0x102c)
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_WDT_TIMER1_TIMEOUT_TRIG_LOW                  (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_WDT_TIMER1_TIMEOUT_TRIG_MASK                 (0x1)
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_WDT_TIMER2_TIMEOUT_TRIG_LOW                  (1)
#define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_WDT_TIMER2_TIMEOUT_TRIG_MASK                 (0x2)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R                                                    (0x1030)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R                                                    (0x1030)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL31_TRIG_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL31_TRIG_MASK                  (0x1)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL30_TRIG_LOW                   (1)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL30_TRIG_MASK                  (0x2)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL29_TRIG_LOW                   (2)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL29_TRIG_MASK                  (0x4)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL28_TRIG_LOW                   (3)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL28_TRIG_MASK                  (0x8)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL27_TRIG_LOW                   (4)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL27_TRIG_MASK                  (0x10)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL26_TRIG_LOW                   (5)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL26_TRIG_MASK                  (0x20)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL25_TRIG_LOW                   (6)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL25_TRIG_MASK                  (0x40)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL24_TRIG_LOW                   (7)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL24_TRIG_MASK                  (0x80)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL23_TRIG_LOW                   (8)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL23_TRIG_MASK                  (0x100)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL22_TRIG_LOW                   (9)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL22_TRIG_MASK                  (0x200)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL21_TRIG_LOW                   (10)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL21_TRIG_MASK                  (0x400)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL20_TRIG_LOW                   (11)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL20_TRIG_MASK                  (0x800)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL19_TRIG_LOW                   (12)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL19_TRIG_MASK                  (0x1000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL18_TRIG_LOW                   (13)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL18_TRIG_MASK                  (0x2000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL17_TRIG_LOW                   (14)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL17_TRIG_MASK                  (0x4000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL16_TRIG_LOW                   (15)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL16_TRIG_MASK                  (0x8000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL15_TRIG_LOW                   (16)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL15_TRIG_MASK                  (0x10000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL14_TRIG_LOW                   (17)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL14_TRIG_MASK                  (0x20000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL13_TRIG_LOW                   (18)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL13_TRIG_MASK                  (0x40000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL12_TRIG_LOW                   (19)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL12_TRIG_MASK                  (0x80000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL11_TRIG_LOW                   (20)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL11_TRIG_MASK                  (0x100000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL10_TRIG_LOW                   (21)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL10_TRIG_MASK                  (0x200000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL9_TRIG_LOW                    (22)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL9_TRIG_MASK                   (0x400000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL8_TRIG_LOW                    (23)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL8_TRIG_MASK                   (0x800000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL7_TRIG_LOW                    (24)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL7_TRIG_MASK                   (0x1000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL6_TRIG_LOW                    (25)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL6_TRIG_MASK                   (0x2000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL5_TRIG_LOW                    (26)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL5_TRIG_MASK                   (0x4000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL4_TRIG_LOW                    (27)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL4_TRIG_MASK                   (0x8000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL3_TRIG_LOW                    (28)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL3_TRIG_MASK                   (0x10000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL2_TRIG_LOW                    (29)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL2_TRIG_MASK                   (0x20000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL1_TRIG_LOW                    (30)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL1_TRIG_MASK                   (0x40000000)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL0_TRIG_LOW                    (31)
#define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL0_TRIG_MASK                   (0x80000000)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R                                                    (0x1034)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R                                                    (0x1034)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MCU_SRAM_ECC_COR_TRIG_LOW                    (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MCU_SRAM_ECC_COR_TRIG_MASK                   (0x1)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_CLPRA_MCU_RESET_REQ_TRIG_LOW                 (1)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_CLPRA_MCU_RESET_REQ_TRIG_MASK                (0x2)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_GEN_IN_TOGGLE_TRIG_LOW                       (2)
#define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_GEN_IN_TOGGLE_TRIG_MASK                      (0x4)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R                                                    (0x1038)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R                                                    (0x1038)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL31_TRIG_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL31_TRIG_MASK              (0x1)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL30_TRIG_LOW               (1)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL30_TRIG_MASK              (0x2)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL29_TRIG_LOW               (2)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL29_TRIG_MASK              (0x4)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL28_TRIG_LOW               (3)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL28_TRIG_MASK              (0x8)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL27_TRIG_LOW               (4)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL27_TRIG_MASK              (0x10)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL26_TRIG_LOW               (5)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL26_TRIG_MASK              (0x20)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL25_TRIG_LOW               (6)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL25_TRIG_MASK              (0x40)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL24_TRIG_LOW               (7)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL24_TRIG_MASK              (0x80)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL23_TRIG_LOW               (8)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL23_TRIG_MASK              (0x100)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL22_TRIG_LOW               (9)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL22_TRIG_MASK              (0x200)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL21_TRIG_LOW               (10)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL21_TRIG_MASK              (0x400)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL20_TRIG_LOW               (11)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL20_TRIG_MASK              (0x800)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL19_TRIG_LOW               (12)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL19_TRIG_MASK              (0x1000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL18_TRIG_LOW               (13)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL18_TRIG_MASK              (0x2000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL17_TRIG_LOW               (14)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL17_TRIG_MASK              (0x4000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL16_TRIG_LOW               (15)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL16_TRIG_MASK              (0x8000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL15_TRIG_LOW               (16)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL15_TRIG_MASK              (0x10000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL14_TRIG_LOW               (17)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL14_TRIG_MASK              (0x20000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL13_TRIG_LOW               (18)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL13_TRIG_MASK              (0x40000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL12_TRIG_LOW               (19)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL12_TRIG_MASK              (0x80000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL11_TRIG_LOW               (20)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL11_TRIG_MASK              (0x100000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL10_TRIG_LOW               (21)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL10_TRIG_MASK              (0x200000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL9_TRIG_LOW                (22)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL9_TRIG_MASK               (0x400000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL8_TRIG_LOW                (23)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL8_TRIG_MASK               (0x800000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL7_TRIG_LOW                (24)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL7_TRIG_MASK               (0x1000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL6_TRIG_LOW                (25)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL6_TRIG_MASK               (0x2000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL5_TRIG_LOW                (26)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL5_TRIG_MASK               (0x4000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL4_TRIG_LOW                (27)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL4_TRIG_MASK               (0x8000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL3_TRIG_LOW                (28)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL3_TRIG_MASK               (0x10000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL2_TRIG_LOW                (29)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL2_TRIG_MASK               (0x20000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL1_TRIG_LOW                (30)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL1_TRIG_MASK               (0x40000000)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL0_TRIG_LOW                (31)
#define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL0_TRIG_MASK               (0x80000000)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R                                 (0x1100)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R                                 (0x1100)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R                                 (0x1104)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R                                 (0x1104)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R                                   (0x1108)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R                                   (0x1108)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R                                   (0x110c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R                                   (0x110c)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R                                   (0x1110)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R                                   (0x1110)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R                                   (0x1114)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R                                   (0x1114)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R                                   (0x1118)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R                                   (0x1118)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R                                   (0x111c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R                                   (0x111c)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R                                   (0x1120)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R                                   (0x1120)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R                                   (0x1124)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R                                   (0x1124)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R                                   (0x1128)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R                                   (0x1128)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R                                   (0x112c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R                                   (0x112c)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R                                  (0x1130)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R                                  (0x1130)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R                                  (0x1134)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R                                  (0x1134)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R                                  (0x1138)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R                                  (0x1138)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R                                  (0x113c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R                                  (0x113c)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R                                  (0x1140)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R                                  (0x1140)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R                                  (0x1144)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R                                  (0x1144)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R                                  (0x1148)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R                                  (0x1148)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R                                  (0x114c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R                                  (0x114c)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R                                  (0x1150)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R                                  (0x1150)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R                                  (0x1154)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R                                  (0x1154)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R                                  (0x1158)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R                                  (0x1158)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R                                  (0x115c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R                                  (0x115c)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R                                  (0x1160)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R                                  (0x1160)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R                                  (0x1164)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R                                  (0x1164)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R                                  (0x1168)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R                                  (0x1168)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R                                  (0x116c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R                                  (0x116c)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R                                  (0x1170)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R                                  (0x1170)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R                                  (0x1174)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R                                  (0x1174)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R                                  (0x1178)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R                                  (0x1178)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R                                  (0x117c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R                                  (0x117c)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R                                  (0x1180)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R                                  (0x1180)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R                                  (0x1184)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R                                  (0x1184)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R                                   (0x1200)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R                                   (0x1200)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_CLPRA_MCU_RESET_REQ_INTR_COUNT_R                                (0x1204)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_CLPRA_MCU_RESET_REQ_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_CLPRA_MCU_RESET_REQ_INTR_COUNT_R                                (0x1204)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R                                      (0x1208)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R                                      (0x1208)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R                               (0x120c)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R                               (0x120c)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R                               (0x1210)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R                               (0x1210)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R                               (0x1214)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R                               (0x1214)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R                               (0x1218)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R                               (0x1218)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R                               (0x121c)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R                               (0x121c)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R                               (0x1220)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R                               (0x1220)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R                               (0x1224)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R                               (0x1224)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R                               (0x1228)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R                               (0x1228)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R                               (0x122c)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R                               (0x122c)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R                               (0x1230)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R                               (0x1230)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R                              (0x1234)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R                              (0x1234)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R                              (0x1238)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R                              (0x1238)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R                              (0x123c)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R                              (0x123c)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R                              (0x1240)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R                              (0x1240)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R                              (0x1244)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R                              (0x1244)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R                              (0x1248)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R                              (0x1248)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R                              (0x124c)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R                              (0x124c)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R                              (0x1250)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R                              (0x1250)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R                              (0x1254)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R                              (0x1254)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R                              (0x1258)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R                              (0x1258)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R                              (0x125c)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R                              (0x125c)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R                              (0x1260)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R                              (0x1260)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R                              (0x1264)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R                              (0x1264)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R                              (0x1268)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R                              (0x1268)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R                              (0x126c)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R                              (0x126c)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R                              (0x1270)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R                              (0x1270)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R                              (0x1274)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R                              (0x1274)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R                              (0x1278)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R                              (0x1278)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R                              (0x127c)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R                              (0x127c)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R                              (0x1280)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R                              (0x1280)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R                              (0x1284)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R                              (0x1284)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R                              (0x1288)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R                              (0x1288)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R                            (0x1300)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R                            (0x1300)
#define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_PULSE_LOW                  (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_PULSE_MASK                 (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R                            (0x1304)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R                            (0x1304)
#define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_PULSE_LOW                  (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_PULSE_MASK                 (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R                              (0x1308)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R                              (0x1308)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R_PULSE_MASK                   (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R                              (0x130c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R                              (0x130c)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R_PULSE_MASK                   (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R                              (0x1310)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R                              (0x1310)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R_PULSE_MASK                   (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R                              (0x1314)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R                              (0x1314)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R_PULSE_MASK                   (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R                              (0x1318)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R                              (0x1318)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R_PULSE_MASK                   (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R                              (0x131c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R                              (0x131c)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R_PULSE_MASK                   (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R                              (0x1320)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R                              (0x1320)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R_PULSE_MASK                   (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R                              (0x1324)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R                              (0x1324)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R_PULSE_MASK                   (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R                              (0x1328)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R                              (0x1328)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R_PULSE_MASK                   (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R                              (0x132c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R                              (0x132c)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R_PULSE_MASK                   (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R                             (0x1330)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R                             (0x1330)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R                             (0x1334)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R                             (0x1334)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R                             (0x1338)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R                             (0x1338)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R                             (0x133c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R                             (0x133c)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R                             (0x1340)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R                             (0x1340)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R                             (0x1344)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R                             (0x1344)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R                             (0x1348)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R                             (0x1348)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R                             (0x134c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R                             (0x134c)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R                             (0x1350)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R                             (0x1350)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R                             (0x1354)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R                             (0x1354)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R                             (0x1358)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R                             (0x1358)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R                             (0x135c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R                             (0x135c)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R                             (0x1360)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R                             (0x1360)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R                             (0x1364)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R                             (0x1364)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R                             (0x1368)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R                             (0x1368)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R                             (0x136c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R                             (0x136c)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R                             (0x1370)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R                             (0x1370)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R                             (0x1374)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R                             (0x1374)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R                             (0x1378)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R                             (0x1378)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R                             (0x137c)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R                             (0x137c)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R                             (0x1380)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R                             (0x1380)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R                             (0x1384)
#ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R                             (0x1384)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R                              (0x1388)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R                              (0x1388)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R_PULSE_MASK                   (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_CLPRA_MCU_RESET_REQ_INTR_COUNT_INCR_R                           (0x138c)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_CLPRA_MCU_RESET_REQ_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_CLPRA_MCU_RESET_REQ_INTR_COUNT_INCR_R                           (0x138c)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_CLPRA_MCU_RESET_REQ_INTR_COUNT_INCR_R_PULSE_LOW                 (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_CLPRA_MCU_RESET_REQ_INTR_COUNT_INCR_R_PULSE_MASK                (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R                                 (0x1390)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R                                 (0x1390)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R_PULSE_MASK                      (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R                          (0x1394)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R                          (0x1394)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R_PULSE_LOW                (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R_PULSE_MASK               (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R                          (0x1398)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R                          (0x1398)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R_PULSE_LOW                (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R_PULSE_MASK               (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R                          (0x139c)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R                          (0x139c)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R_PULSE_LOW                (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R_PULSE_MASK               (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R                          (0x13a0)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R                          (0x13a0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R_PULSE_LOW                (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R_PULSE_MASK               (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R                          (0x13a4)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R                          (0x13a4)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R_PULSE_LOW                (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R_PULSE_MASK               (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R                          (0x13a8)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R                          (0x13a8)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R_PULSE_LOW                (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R_PULSE_MASK               (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R                          (0x13ac)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R                          (0x13ac)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R_PULSE_LOW                (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R_PULSE_MASK               (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R                          (0x13b0)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R                          (0x13b0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R_PULSE_LOW                (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R_PULSE_MASK               (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R                          (0x13b4)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R                          (0x13b4)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R_PULSE_LOW                (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R_PULSE_MASK               (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R                          (0x13b8)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R                          (0x13b8)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R_PULSE_LOW                (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R_PULSE_MASK               (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R                         (0x13bc)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R                         (0x13bc)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R                         (0x13c0)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R                         (0x13c0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R                         (0x13c4)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R                         (0x13c4)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R                         (0x13c8)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R                         (0x13c8)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R                         (0x13cc)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R                         (0x13cc)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R                         (0x13d0)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R                         (0x13d0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R                         (0x13d4)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R                         (0x13d4)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R                         (0x13d8)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R                         (0x13d8)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R                         (0x13dc)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R                         (0x13dc)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R                         (0x13e0)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R                         (0x13e0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R                         (0x13e4)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R                         (0x13e4)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R                         (0x13e8)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R                         (0x13e8)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R                         (0x13ec)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R                         (0x13ec)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R                         (0x13f0)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R                         (0x13f0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R                         (0x13f4)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R                         (0x13f4)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R                         (0x13f8)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R                         (0x13f8)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R                         (0x13fc)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R                         (0x13fc)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R                         (0x1400)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R                         (0x1400)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R                         (0x1404)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R                         (0x1404)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R                         (0x1408)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R                         (0x1408)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R                         (0x140c)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R                         (0x140c)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R                         (0x1410)
#ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R                         (0x1410)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R_PULSE_LOW               (0)
#define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R_PULSE_MASK              (0x1)
#endif


#endif