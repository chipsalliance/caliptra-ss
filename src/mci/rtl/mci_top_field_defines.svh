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
`ifndef MCI_TOP_FIELD_DEFINES_HEADER
`define MCI_TOP_FIELD_DEFINES_HEADER


`ifndef MCI_REG_HW_CAPABILITIES
`define MCI_REG_HW_CAPABILITIES                                                                     (32'h0)
`endif
`ifndef MCI_REG_FW_CAPABILITIES
`define MCI_REG_FW_CAPABILITIES                                                                     (32'h4)
`endif
`ifndef MCI_REG_CAP_LOCK
`define MCI_REG_CAP_LOCK                                                                            (32'h8)
`define MCI_REG_CAP_LOCK_LOCK_LOW                                                                   (0)
`define MCI_REG_CAP_LOCK_LOCK_MASK                                                                  (32'h1)
`endif
`ifndef MCI_REG_HW_REV_ID
`define MCI_REG_HW_REV_ID                                                                           (32'hc)
`define MCI_REG_HW_REV_ID_MC_GENERATION_LOW                                                         (0)
`define MCI_REG_HW_REV_ID_MC_GENERATION_MASK                                                        (32'hffff)
`endif
`ifndef MCI_REG_FW_REV_ID_0
`define MCI_REG_FW_REV_ID_0                                                                         (32'h10)
`endif
`ifndef MCI_REG_FW_REV_ID_1
`define MCI_REG_FW_REV_ID_1                                                                         (32'h14)
`endif
`ifndef MCI_REG_HW_CONFIG0
`define MCI_REG_HW_CONFIG0                                                                          (32'h18)
`define MCI_REG_HW_CONFIG0_MCI_MBOX1_SRAM_SIZE_LOW                                                  (0)
`define MCI_REG_HW_CONFIG0_MCI_MBOX1_SRAM_SIZE_MASK                                                 (32'hfff)
`define MCI_REG_HW_CONFIG0_MCI_MBOX0_SRAM_SIZE_LOW                                                  (12)
`define MCI_REG_HW_CONFIG0_MCI_MBOX0_SRAM_SIZE_MASK                                                 (32'hfff000)
`endif
`ifndef MCI_REG_HW_CONFIG1
`define MCI_REG_HW_CONFIG1                                                                          (32'h1c)
`define MCI_REG_HW_CONFIG1_MIN_MCU_RST_COUNTER_WIDTH_LOW                                            (0)
`define MCI_REG_HW_CONFIG1_MIN_MCU_RST_COUNTER_WIDTH_MASK                                           (32'h1f)
`define MCI_REG_HW_CONFIG1_MCU_SRAM_SIZE_LOW                                                        (5)
`define MCI_REG_HW_CONFIG1_MCU_SRAM_SIZE_MASK                                                       (32'h1ffe0)
`endif
`ifndef MCI_REG_FW_FLOW_STATUS
`define MCI_REG_FW_FLOW_STATUS                                                                      (32'h20)
`endif
`ifndef MCI_REG_HW_FLOW_STATUS
`define MCI_REG_HW_FLOW_STATUS                                                                      (32'h24)
`define MCI_REG_HW_FLOW_STATUS_BOOT_FSM_LOW                                                         (0)
`define MCI_REG_HW_FLOW_STATUS_BOOT_FSM_MASK                                                        (32'hf)
`endif
`ifndef MCI_REG_RESET_REASON
`define MCI_REG_RESET_REASON                                                                        (32'h28)
`define MCI_REG_RESET_REASON_FW_HITLESS_UPD_RESET_LOW                                               (0)
`define MCI_REG_RESET_REASON_FW_HITLESS_UPD_RESET_MASK                                              (32'h1)
`define MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_LOW                                                  (1)
`define MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_MASK                                                 (32'h2)
`define MCI_REG_RESET_REASON_WARM_RESET_LOW                                                         (2)
`define MCI_REG_RESET_REASON_WARM_RESET_MASK                                                        (32'h4)
`endif
`ifndef MCI_REG_RESET_STATUS
`define MCI_REG_RESET_STATUS                                                                        (32'h2c)
`define MCI_REG_RESET_STATUS_CPTRA_RESET_STS_LOW                                                    (0)
`define MCI_REG_RESET_STATUS_CPTRA_RESET_STS_MASK                                                   (32'h1)
`define MCI_REG_RESET_STATUS_MCU_RESET_STS_LOW                                                      (1)
`define MCI_REG_RESET_STATUS_MCU_RESET_STS_MASK                                                     (32'h2)
`endif
`ifndef MCI_REG_SECURITY_STATE
`define MCI_REG_SECURITY_STATE                                                                      (32'h30)
`define MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_LOW                                                 (0)
`define MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_MASK                                                (32'h3)
`define MCI_REG_SECURITY_STATE_DEBUG_LOCKED_LOW                                                     (2)
`define MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK                                                    (32'h4)
`define MCI_REG_SECURITY_STATE_SCAN_MODE_LOW                                                        (3)
`define MCI_REG_SECURITY_STATE_SCAN_MODE_MASK                                                       (32'h8)
`endif
`ifndef MCI_REG_HW_ERROR_FATAL
`define MCI_REG_HW_ERROR_FATAL                                                                      (32'h40)
`define MCI_REG_HW_ERROR_FATAL_MCU_SRAM_ECC_UNC_LOW                                                 (0)
`define MCI_REG_HW_ERROR_FATAL_MCU_SRAM_ECC_UNC_MASK                                                (32'h1)
`define MCI_REG_HW_ERROR_FATAL_NMI_PIN_LOW                                                          (1)
`define MCI_REG_HW_ERROR_FATAL_NMI_PIN_MASK                                                         (32'h2)
`define MCI_REG_HW_ERROR_FATAL_MCU_SRAM_DMI_AXI_COLLISION_LOW                                       (2)
`define MCI_REG_HW_ERROR_FATAL_MCU_SRAM_DMI_AXI_COLLISION_MASK                                      (32'h4)
`endif
`ifndef MCI_REG_AGG_ERROR_FATAL
`define MCI_REG_AGG_ERROR_FATAL                                                                     (32'h44)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL31_LOW                                               (0)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL31_MASK                                              (32'h1)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL30_LOW                                               (1)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL30_MASK                                              (32'h2)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL29_LOW                                               (2)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL29_MASK                                              (32'h4)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL28_LOW                                               (3)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL28_MASK                                              (32'h8)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL27_LOW                                               (4)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL27_MASK                                              (32'h10)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL26_LOW                                               (5)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL26_MASK                                              (32'h20)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL25_LOW                                               (6)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL25_MASK                                              (32'h40)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL24_LOW                                               (7)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL24_MASK                                              (32'h80)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL23_LOW                                               (8)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL23_MASK                                              (32'h100)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL22_LOW                                               (9)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL22_MASK                                              (32'h200)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL21_LOW                                               (10)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL21_MASK                                              (32'h400)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL20_LOW                                               (11)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL20_MASK                                              (32'h800)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL19_LOW                                               (12)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL19_MASK                                              (32'h1000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL18_LOW                                               (13)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL18_MASK                                              (32'h2000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL17_LOW                                               (14)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL17_MASK                                              (32'h4000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL16_LOW                                               (15)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL16_MASK                                              (32'h8000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL15_LOW                                               (16)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL15_MASK                                              (32'h10000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL14_LOW                                               (17)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL14_MASK                                              (32'h20000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL13_LOW                                               (18)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL13_MASK                                              (32'h40000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL12_LOW                                               (19)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL12_MASK                                              (32'h80000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL11_LOW                                               (20)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL11_MASK                                              (32'h100000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL10_LOW                                               (21)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL10_MASK                                              (32'h200000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL9_LOW                                                (22)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL9_MASK                                               (32'h400000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL8_LOW                                                (23)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL8_MASK                                               (32'h800000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL7_LOW                                                (24)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL7_MASK                                               (32'h1000000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL6_LOW                                                (25)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL6_MASK                                               (32'h2000000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL5_LOW                                                (26)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL5_MASK                                               (32'h4000000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL4_LOW                                                (27)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL4_MASK                                               (32'h8000000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL3_LOW                                                (28)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL3_MASK                                               (32'h10000000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL2_LOW                                                (29)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL2_MASK                                               (32'h20000000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL1_LOW                                                (30)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL1_MASK                                               (32'h40000000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL0_LOW                                                (31)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL0_MASK                                               (32'h80000000)
`endif
`ifndef MCI_REG_HW_ERROR_NON_FATAL
`define MCI_REG_HW_ERROR_NON_FATAL                                                                  (32'h48)
`define MCI_REG_HW_ERROR_NON_FATAL_MBOX0_PROT_NO_LOCK_LOW                                           (0)
`define MCI_REG_HW_ERROR_NON_FATAL_MBOX0_PROT_NO_LOCK_MASK                                          (32'h1)
`define MCI_REG_HW_ERROR_NON_FATAL_MBOX1_PROT_NO_LOCK_LOW                                           (1)
`define MCI_REG_HW_ERROR_NON_FATAL_MBOX1_PROT_NO_LOCK_MASK                                          (32'h2)
`define MCI_REG_HW_ERROR_NON_FATAL_MBOX0_PROT_OOO_LOW                                               (2)
`define MCI_REG_HW_ERROR_NON_FATAL_MBOX0_PROT_OOO_MASK                                              (32'h4)
`define MCI_REG_HW_ERROR_NON_FATAL_MBOX1_PROT_OOO_LOW                                               (3)
`define MCI_REG_HW_ERROR_NON_FATAL_MBOX1_PROT_OOO_MASK                                              (32'h8)
`define MCI_REG_HW_ERROR_NON_FATAL_MBOX0_ECC_UNC_LOW                                                (4)
`define MCI_REG_HW_ERROR_NON_FATAL_MBOX0_ECC_UNC_MASK                                               (32'h10)
`define MCI_REG_HW_ERROR_NON_FATAL_MBOX1_ECC_UNC_LOW                                                (5)
`define MCI_REG_HW_ERROR_NON_FATAL_MBOX1_ECC_UNC_MASK                                               (32'h20)
`endif
`ifndef MCI_REG_AGG_ERROR_NON_FATAL
`define MCI_REG_AGG_ERROR_NON_FATAL                                                                 (32'h4c)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL31_LOW                                       (0)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL31_MASK                                      (32'h1)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL30_LOW                                       (1)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL30_MASK                                      (32'h2)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL29_LOW                                       (2)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL29_MASK                                      (32'h4)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL28_LOW                                       (3)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL28_MASK                                      (32'h8)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL27_LOW                                       (4)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL27_MASK                                      (32'h10)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL26_LOW                                       (5)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL26_MASK                                      (32'h20)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL25_LOW                                       (6)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL25_MASK                                      (32'h40)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL24_LOW                                       (7)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL24_MASK                                      (32'h80)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL23_LOW                                       (8)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL23_MASK                                      (32'h100)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL22_LOW                                       (9)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL22_MASK                                      (32'h200)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL21_LOW                                       (10)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL21_MASK                                      (32'h400)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL20_LOW                                       (11)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL20_MASK                                      (32'h800)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL19_LOW                                       (12)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL19_MASK                                      (32'h1000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL18_LOW                                       (13)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL18_MASK                                      (32'h2000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL17_LOW                                       (14)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL17_MASK                                      (32'h4000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL16_LOW                                       (15)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL16_MASK                                      (32'h8000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL15_LOW                                       (16)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL15_MASK                                      (32'h10000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL14_LOW                                       (17)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL14_MASK                                      (32'h20000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL13_LOW                                       (18)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL13_MASK                                      (32'h40000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL12_LOW                                       (19)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL12_MASK                                      (32'h80000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL11_LOW                                       (20)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL11_MASK                                      (32'h100000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL10_LOW                                       (21)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL10_MASK                                      (32'h200000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL9_LOW                                        (22)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL9_MASK                                       (32'h400000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL8_LOW                                        (23)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL8_MASK                                       (32'h800000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL7_LOW                                        (24)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL7_MASK                                       (32'h1000000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL6_LOW                                        (25)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL6_MASK                                       (32'h2000000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL5_LOW                                        (26)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL5_MASK                                       (32'h4000000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL4_LOW                                        (27)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL4_MASK                                       (32'h8000000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL3_LOW                                        (28)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL3_MASK                                       (32'h10000000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL2_LOW                                        (29)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL2_MASK                                       (32'h20000000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL1_LOW                                        (30)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL1_MASK                                       (32'h40000000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL0_LOW                                        (31)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL0_MASK                                       (32'h80000000)
`endif
`ifndef MCI_REG_FW_ERROR_FATAL
`define MCI_REG_FW_ERROR_FATAL                                                                      (32'h50)
`endif
`ifndef MCI_REG_FW_ERROR_NON_FATAL
`define MCI_REG_FW_ERROR_NON_FATAL                                                                  (32'h54)
`endif
`ifndef MCI_REG_HW_ERROR_ENC
`define MCI_REG_HW_ERROR_ENC                                                                        (32'h58)
`endif
`ifndef MCI_REG_FW_ERROR_ENC
`define MCI_REG_FW_ERROR_ENC                                                                        (32'h5c)
`endif
`ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_0
`define MCI_REG_FW_EXTENDED_ERROR_INFO_0                                                            (32'h60)
`endif
`ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_1
`define MCI_REG_FW_EXTENDED_ERROR_INFO_1                                                            (32'h64)
`endif
`ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_2
`define MCI_REG_FW_EXTENDED_ERROR_INFO_2                                                            (32'h68)
`endif
`ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_3
`define MCI_REG_FW_EXTENDED_ERROR_INFO_3                                                            (32'h6c)
`endif
`ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_4
`define MCI_REG_FW_EXTENDED_ERROR_INFO_4                                                            (32'h70)
`endif
`ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_5
`define MCI_REG_FW_EXTENDED_ERROR_INFO_5                                                            (32'h74)
`endif
`ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_6
`define MCI_REG_FW_EXTENDED_ERROR_INFO_6                                                            (32'h78)
`endif
`ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_7
`define MCI_REG_FW_EXTENDED_ERROR_INFO_7                                                            (32'h7c)
`endif
`ifndef MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK
`define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK                                                        (32'h80)
`define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_MCU_SRAM_ECC_UNC_LOW                              (0)
`define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_MCU_SRAM_ECC_UNC_MASK                             (32'h1)
`define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_NMI_PIN_LOW                                       (1)
`define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_NMI_PIN_MASK                                      (32'h2)
`define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_MCU_SRAM_DMI_AXI_COLLISION_LOW                    (2)
`define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_MCU_SRAM_DMI_AXI_COLLISION_MASK                   (32'h4)
`endif
`ifndef MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK                                                    (32'h84)
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX0_PROT_NO_LOCK_LOW                        (0)
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX0_PROT_NO_LOCK_MASK                       (32'h1)
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX1_PROT_NO_LOCK_LOW                        (1)
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX1_PROT_NO_LOCK_MASK                       (32'h2)
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX0_PROT_OOO_LOW                            (2)
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX0_PROT_OOO_MASK                           (32'h4)
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX1_PROT_OOO_LOW                            (3)
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX1_PROT_OOO_MASK                           (32'h8)
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX0_ECC_UNC_LOW                             (4)
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX0_ECC_UNC_MASK                            (32'h10)
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX1_ECC_UNC_LOW                             (5)
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX1_ECC_UNC_MASK                            (32'h20)
`endif
`ifndef MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK                                                       (32'h88)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL31_LOW                            (0)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL31_MASK                           (32'h1)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL30_LOW                            (1)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL30_MASK                           (32'h2)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL29_LOW                            (2)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL29_MASK                           (32'h4)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL28_LOW                            (3)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL28_MASK                           (32'h8)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL27_LOW                            (4)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL27_MASK                           (32'h10)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL26_LOW                            (5)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL26_MASK                           (32'h20)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL25_LOW                            (6)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL25_MASK                           (32'h40)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL24_LOW                            (7)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL24_MASK                           (32'h80)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL23_LOW                            (8)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL23_MASK                           (32'h100)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL22_LOW                            (9)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL22_MASK                           (32'h200)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL21_LOW                            (10)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL21_MASK                           (32'h400)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL20_LOW                            (11)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL20_MASK                           (32'h800)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL19_LOW                            (12)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL19_MASK                           (32'h1000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL18_LOW                            (13)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL18_MASK                           (32'h2000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL17_LOW                            (14)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL17_MASK                           (32'h4000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL16_LOW                            (15)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL16_MASK                           (32'h8000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL15_LOW                            (16)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL15_MASK                           (32'h10000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL14_LOW                            (17)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL14_MASK                           (32'h20000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL13_LOW                            (18)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL13_MASK                           (32'h40000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL12_LOW                            (19)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL12_MASK                           (32'h80000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL11_LOW                            (20)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL11_MASK                           (32'h100000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL10_LOW                            (21)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL10_MASK                           (32'h200000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL9_LOW                             (22)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL9_MASK                            (32'h400000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL8_LOW                             (23)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL8_MASK                            (32'h800000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL7_LOW                             (24)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL7_MASK                            (32'h1000000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL6_LOW                             (25)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL6_MASK                            (32'h2000000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL5_LOW                             (26)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL5_MASK                            (32'h4000000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL4_LOW                             (27)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL4_MASK                            (32'h8000000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL3_LOW                             (28)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL3_MASK                            (32'h10000000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL2_LOW                             (29)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL2_MASK                            (32'h20000000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL1_LOW                             (30)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL1_MASK                            (32'h40000000)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL0_LOW                             (31)
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL0_MASK                            (32'h80000000)
`endif
`ifndef MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK                                                   (32'h8c)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL31_LOW                    (0)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL31_MASK                   (32'h1)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL30_LOW                    (1)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL30_MASK                   (32'h2)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL29_LOW                    (2)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL29_MASK                   (32'h4)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL28_LOW                    (3)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL28_MASK                   (32'h8)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL27_LOW                    (4)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL27_MASK                   (32'h10)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL26_LOW                    (5)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL26_MASK                   (32'h20)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL25_LOW                    (6)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL25_MASK                   (32'h40)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL24_LOW                    (7)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL24_MASK                   (32'h80)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL23_LOW                    (8)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL23_MASK                   (32'h100)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL22_LOW                    (9)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL22_MASK                   (32'h200)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL21_LOW                    (10)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL21_MASK                   (32'h400)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL20_LOW                    (11)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL20_MASK                   (32'h800)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL19_LOW                    (12)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL19_MASK                   (32'h1000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL18_LOW                    (13)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL18_MASK                   (32'h2000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL17_LOW                    (14)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL17_MASK                   (32'h4000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL16_LOW                    (15)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL16_MASK                   (32'h8000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL15_LOW                    (16)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL15_MASK                   (32'h10000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL14_LOW                    (17)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL14_MASK                   (32'h20000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL13_LOW                    (18)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL13_MASK                   (32'h40000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL12_LOW                    (19)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL12_MASK                   (32'h80000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL11_LOW                    (20)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL11_MASK                   (32'h100000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL10_LOW                    (21)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL10_MASK                   (32'h200000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL9_LOW                     (22)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL9_MASK                    (32'h400000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL8_LOW                     (23)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL8_MASK                    (32'h800000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL7_LOW                     (24)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL7_MASK                    (32'h1000000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL6_LOW                     (25)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL6_MASK                    (32'h2000000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL5_LOW                     (26)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL5_MASK                    (32'h4000000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL4_LOW                     (27)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL4_MASK                    (32'h8000000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL3_LOW                     (28)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL3_MASK                    (32'h10000000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL2_LOW                     (29)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL2_MASK                    (32'h20000000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL1_LOW                     (30)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL1_MASK                    (32'h40000000)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL0_LOW                     (31)
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL0_MASK                    (32'h80000000)
`endif
`ifndef MCI_REG_INTERNAL_FW_ERROR_FATAL_MASK
`define MCI_REG_INTERNAL_FW_ERROR_FATAL_MASK                                                        (32'h90)
`endif
`ifndef MCI_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK
`define MCI_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK                                                    (32'h94)
`endif
`ifndef MCI_REG_WDT_TIMER1_EN
`define MCI_REG_WDT_TIMER1_EN                                                                       (32'ha0)
`define MCI_REG_WDT_TIMER1_EN_TIMER1_EN_LOW                                                         (0)
`define MCI_REG_WDT_TIMER1_EN_TIMER1_EN_MASK                                                        (32'h1)
`endif
`ifndef MCI_REG_WDT_TIMER1_CTRL
`define MCI_REG_WDT_TIMER1_CTRL                                                                     (32'ha4)
`define MCI_REG_WDT_TIMER1_CTRL_TIMER1_RESTART_LOW                                                  (0)
`define MCI_REG_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK                                                 (32'h1)
`endif
`ifndef MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_0
`define MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_0                                                         (32'ha8)
`endif
`ifndef MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_1
`define MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_1                                                         (32'hac)
`endif
`ifndef MCI_REG_WDT_TIMER2_EN
`define MCI_REG_WDT_TIMER2_EN                                                                       (32'hb0)
`define MCI_REG_WDT_TIMER2_EN_TIMER2_EN_LOW                                                         (0)
`define MCI_REG_WDT_TIMER2_EN_TIMER2_EN_MASK                                                        (32'h1)
`endif
`ifndef MCI_REG_WDT_TIMER2_CTRL
`define MCI_REG_WDT_TIMER2_CTRL                                                                     (32'hb4)
`define MCI_REG_WDT_TIMER2_CTRL_TIMER2_RESTART_LOW                                                  (0)
`define MCI_REG_WDT_TIMER2_CTRL_TIMER2_RESTART_MASK                                                 (32'h1)
`endif
`ifndef MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_0
`define MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_0                                                         (32'hb8)
`endif
`ifndef MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_1
`define MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_1                                                         (32'hbc)
`endif
`ifndef MCI_REG_WDT_STATUS
`define MCI_REG_WDT_STATUS                                                                          (32'hc0)
`define MCI_REG_WDT_STATUS_T1_TIMEOUT_LOW                                                           (0)
`define MCI_REG_WDT_STATUS_T1_TIMEOUT_MASK                                                          (32'h1)
`define MCI_REG_WDT_STATUS_T2_TIMEOUT_LOW                                                           (1)
`define MCI_REG_WDT_STATUS_T2_TIMEOUT_MASK                                                          (32'h2)
`endif
`ifndef MCI_REG_WDT_CFG_0
`define MCI_REG_WDT_CFG_0                                                                           (32'hd0)
`endif
`ifndef MCI_REG_WDT_CFG_1
`define MCI_REG_WDT_CFG_1                                                                           (32'hd4)
`endif
`ifndef MCI_REG_MCU_TIMER_CONFIG
`define MCI_REG_MCU_TIMER_CONFIG                                                                    (32'he0)
`endif
`ifndef MCI_REG_MCU_RV_MTIME_L
`define MCI_REG_MCU_RV_MTIME_L                                                                      (32'he4)
`endif
`ifndef MCI_REG_MCU_RV_MTIME_H
`define MCI_REG_MCU_RV_MTIME_H                                                                      (32'he8)
`endif
`ifndef MCI_REG_MCU_RV_MTIMECMP_L
`define MCI_REG_MCU_RV_MTIMECMP_L                                                                   (32'hec)
`endif
`ifndef MCI_REG_MCU_RV_MTIMECMP_H
`define MCI_REG_MCU_RV_MTIMECMP_H                                                                   (32'hf0)
`endif
`ifndef MCI_REG_RESET_REQUEST
`define MCI_REG_RESET_REQUEST                                                                       (32'h100)
`define MCI_REG_RESET_REQUEST_MCU_REQ_LOW                                                           (0)
`define MCI_REG_RESET_REQUEST_MCU_REQ_MASK                                                          (32'h1)
`endif
`ifndef MCI_REG_MCI_BOOTFSM_GO
`define MCI_REG_MCI_BOOTFSM_GO                                                                      (32'h104)
`define MCI_REG_MCI_BOOTFSM_GO_GO_LOW                                                               (0)
`define MCI_REG_MCI_BOOTFSM_GO_GO_MASK                                                              (32'h1)
`endif
`ifndef MCI_REG_FW_SRAM_EXEC_REGION_SIZE
`define MCI_REG_FW_SRAM_EXEC_REGION_SIZE                                                            (32'h108)
`define MCI_REG_FW_SRAM_EXEC_REGION_SIZE_SIZE_LOW                                                   (0)
`define MCI_REG_FW_SRAM_EXEC_REGION_SIZE_SIZE_MASK                                                  (32'hffff)
`endif
`ifndef MCI_REG_MCU_NMI_VECTOR
`define MCI_REG_MCU_NMI_VECTOR                                                                      (32'h10c)
`endif
`ifndef MCI_REG_MCU_RESET_VECTOR
`define MCI_REG_MCU_RESET_VECTOR                                                                    (32'h110)
`endif
`ifndef MCI_REG_MBOX0_VALID_AXI_USER_0
`define MCI_REG_MBOX0_VALID_AXI_USER_0                                                              (32'h180)
`endif
`ifndef MCI_REG_MBOX0_VALID_AXI_USER_1
`define MCI_REG_MBOX0_VALID_AXI_USER_1                                                              (32'h184)
`endif
`ifndef MCI_REG_MBOX0_VALID_AXI_USER_2
`define MCI_REG_MBOX0_VALID_AXI_USER_2                                                              (32'h188)
`endif
`ifndef MCI_REG_MBOX0_VALID_AXI_USER_3
`define MCI_REG_MBOX0_VALID_AXI_USER_3                                                              (32'h18c)
`endif
`ifndef MCI_REG_MBOX0_VALID_AXI_USER_4
`define MCI_REG_MBOX0_VALID_AXI_USER_4                                                              (32'h190)
`endif
`ifndef MCI_REG_MBOX0_AXI_USER_LOCK_0
`define MCI_REG_MBOX0_AXI_USER_LOCK_0                                                               (32'h1a0)
`define MCI_REG_MBOX0_AXI_USER_LOCK_0_LOCK_LOW                                                      (0)
`define MCI_REG_MBOX0_AXI_USER_LOCK_0_LOCK_MASK                                                     (32'h1)
`endif
`ifndef MCI_REG_MBOX0_AXI_USER_LOCK_1
`define MCI_REG_MBOX0_AXI_USER_LOCK_1                                                               (32'h1a4)
`define MCI_REG_MBOX0_AXI_USER_LOCK_1_LOCK_LOW                                                      (0)
`define MCI_REG_MBOX0_AXI_USER_LOCK_1_LOCK_MASK                                                     (32'h1)
`endif
`ifndef MCI_REG_MBOX0_AXI_USER_LOCK_2
`define MCI_REG_MBOX0_AXI_USER_LOCK_2                                                               (32'h1a8)
`define MCI_REG_MBOX0_AXI_USER_LOCK_2_LOCK_LOW                                                      (0)
`define MCI_REG_MBOX0_AXI_USER_LOCK_2_LOCK_MASK                                                     (32'h1)
`endif
`ifndef MCI_REG_MBOX0_AXI_USER_LOCK_3
`define MCI_REG_MBOX0_AXI_USER_LOCK_3                                                               (32'h1ac)
`define MCI_REG_MBOX0_AXI_USER_LOCK_3_LOCK_LOW                                                      (0)
`define MCI_REG_MBOX0_AXI_USER_LOCK_3_LOCK_MASK                                                     (32'h1)
`endif
`ifndef MCI_REG_MBOX0_AXI_USER_LOCK_4
`define MCI_REG_MBOX0_AXI_USER_LOCK_4                                                               (32'h1b0)
`define MCI_REG_MBOX0_AXI_USER_LOCK_4_LOCK_LOW                                                      (0)
`define MCI_REG_MBOX0_AXI_USER_LOCK_4_LOCK_MASK                                                     (32'h1)
`endif
`ifndef MCI_REG_MBOX1_VALID_AXI_USER_0
`define MCI_REG_MBOX1_VALID_AXI_USER_0                                                              (32'h1c0)
`endif
`ifndef MCI_REG_MBOX1_VALID_AXI_USER_1
`define MCI_REG_MBOX1_VALID_AXI_USER_1                                                              (32'h1c4)
`endif
`ifndef MCI_REG_MBOX1_VALID_AXI_USER_2
`define MCI_REG_MBOX1_VALID_AXI_USER_2                                                              (32'h1c8)
`endif
`ifndef MCI_REG_MBOX1_VALID_AXI_USER_3
`define MCI_REG_MBOX1_VALID_AXI_USER_3                                                              (32'h1cc)
`endif
`ifndef MCI_REG_MBOX1_VALID_AXI_USER_4
`define MCI_REG_MBOX1_VALID_AXI_USER_4                                                              (32'h1d0)
`endif
`ifndef MCI_REG_MBOX1_AXI_USER_LOCK_0
`define MCI_REG_MBOX1_AXI_USER_LOCK_0                                                               (32'h1e0)
`define MCI_REG_MBOX1_AXI_USER_LOCK_0_LOCK_LOW                                                      (0)
`define MCI_REG_MBOX1_AXI_USER_LOCK_0_LOCK_MASK                                                     (32'h1)
`endif
`ifndef MCI_REG_MBOX1_AXI_USER_LOCK_1
`define MCI_REG_MBOX1_AXI_USER_LOCK_1                                                               (32'h1e4)
`define MCI_REG_MBOX1_AXI_USER_LOCK_1_LOCK_LOW                                                      (0)
`define MCI_REG_MBOX1_AXI_USER_LOCK_1_LOCK_MASK                                                     (32'h1)
`endif
`ifndef MCI_REG_MBOX1_AXI_USER_LOCK_2
`define MCI_REG_MBOX1_AXI_USER_LOCK_2                                                               (32'h1e8)
`define MCI_REG_MBOX1_AXI_USER_LOCK_2_LOCK_LOW                                                      (0)
`define MCI_REG_MBOX1_AXI_USER_LOCK_2_LOCK_MASK                                                     (32'h1)
`endif
`ifndef MCI_REG_MBOX1_AXI_USER_LOCK_3
`define MCI_REG_MBOX1_AXI_USER_LOCK_3                                                               (32'h1ec)
`define MCI_REG_MBOX1_AXI_USER_LOCK_3_LOCK_LOW                                                      (0)
`define MCI_REG_MBOX1_AXI_USER_LOCK_3_LOCK_MASK                                                     (32'h1)
`endif
`ifndef MCI_REG_MBOX1_AXI_USER_LOCK_4
`define MCI_REG_MBOX1_AXI_USER_LOCK_4                                                               (32'h1f0)
`define MCI_REG_MBOX1_AXI_USER_LOCK_4_LOCK_LOW                                                      (0)
`define MCI_REG_MBOX1_AXI_USER_LOCK_4_LOCK_MASK                                                     (32'h1)
`endif
`ifndef MCI_REG_SOC_DFT_EN_0
`define MCI_REG_SOC_DFT_EN_0                                                                        (32'h300)
`endif
`ifndef MCI_REG_SOC_DFT_EN_1
`define MCI_REG_SOC_DFT_EN_1                                                                        (32'h304)
`endif
`ifndef MCI_REG_SOC_HW_DEBUG_EN_0
`define MCI_REG_SOC_HW_DEBUG_EN_0                                                                   (32'h308)
`endif
`ifndef MCI_REG_SOC_HW_DEBUG_EN_1
`define MCI_REG_SOC_HW_DEBUG_EN_1                                                                   (32'h30c)
`endif
`ifndef MCI_REG_SOC_PROD_DEBUG_STATE_0
`define MCI_REG_SOC_PROD_DEBUG_STATE_0                                                              (32'h310)
`endif
`ifndef MCI_REG_SOC_PROD_DEBUG_STATE_1
`define MCI_REG_SOC_PROD_DEBUG_STATE_1                                                              (32'h314)
`endif
`ifndef MCI_REG_FC_FIPS_ZERIOZATION
`define MCI_REG_FC_FIPS_ZERIOZATION                                                                 (32'h318)
`endif
`ifndef MCI_REG_GENERIC_INPUT_WIRES_0
`define MCI_REG_GENERIC_INPUT_WIRES_0                                                               (32'h400)
`endif
`ifndef MCI_REG_GENERIC_INPUT_WIRES_1
`define MCI_REG_GENERIC_INPUT_WIRES_1                                                               (32'h404)
`endif
`ifndef MCI_REG_GENERIC_OUTPUT_WIRES_0
`define MCI_REG_GENERIC_OUTPUT_WIRES_0                                                              (32'h408)
`endif
`ifndef MCI_REG_GENERIC_OUTPUT_WIRES_1
`define MCI_REG_GENERIC_OUTPUT_WIRES_1                                                              (32'h40c)
`endif
`ifndef MCI_REG_DEBUG_IN
`define MCI_REG_DEBUG_IN                                                                            (32'h410)
`define MCI_REG_DEBUG_IN_DATA_LOW                                                                   (0)
`define MCI_REG_DEBUG_IN_DATA_MASK                                                                  (32'h1)
`endif
`ifndef MCI_REG_DEBUG_OUT
`define MCI_REG_DEBUG_OUT                                                                           (32'h414)
`define MCI_REG_DEBUG_OUT_DATA_LOW                                                                  (0)
`define MCI_REG_DEBUG_OUT_DATA_MASK                                                                 (32'h1)
`endif
`ifndef MCI_REG_SS_DEBUG_INTENT
`define MCI_REG_SS_DEBUG_INTENT                                                                     (32'h418)
`define MCI_REG_SS_DEBUG_INTENT_DEBUG_INTENT_LOW                                                    (0)
`define MCI_REG_SS_DEBUG_INTENT_DEBUG_INTENT_MASK                                                   (32'h1)
`endif
`ifndef MCI_REG_SS_CONFIG_DONE
`define MCI_REG_SS_CONFIG_DONE                                                                      (32'h440)
`define MCI_REG_SS_CONFIG_DONE_DONE_LOW                                                             (0)
`define MCI_REG_SS_CONFIG_DONE_DONE_MASK                                                            (32'h1)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_0
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_0                                                   (32'h480)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_1
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_1                                                   (32'h484)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_2
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_2                                                   (32'h488)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_3
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_3                                                   (32'h48c)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_4
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_4                                                   (32'h490)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_5
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_5                                                   (32'h494)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_6
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_6                                                   (32'h498)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_7
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_7                                                   (32'h49c)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_8
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_8                                                   (32'h4a0)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_9
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_9                                                   (32'h4a4)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_10
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_10                                                  (32'h4a8)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_11
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_11                                                  (32'h4ac)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_0
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_0                                                   (32'h4b0)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_1
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_1                                                   (32'h4b4)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_2
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_2                                                   (32'h4b8)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_3
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_3                                                   (32'h4bc)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_4
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_4                                                   (32'h4c0)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_5
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_5                                                   (32'h4c4)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_6
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_6                                                   (32'h4c8)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_7
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_7                                                   (32'h4cc)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_8
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_8                                                   (32'h4d0)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_9
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_9                                                   (32'h4d4)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_10
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_10                                                  (32'h4d8)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_11
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_11                                                  (32'h4dc)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_0
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_0                                                   (32'h4e0)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_1
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_1                                                   (32'h4e4)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_2
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_2                                                   (32'h4e8)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_3
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_3                                                   (32'h4ec)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_4
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_4                                                   (32'h4f0)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_5
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_5                                                   (32'h4f4)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_6
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_6                                                   (32'h4f8)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_7
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_7                                                   (32'h4fc)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_8
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_8                                                   (32'h500)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_9
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_9                                                   (32'h504)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_10
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_10                                                  (32'h508)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_11
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_11                                                  (32'h50c)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_0
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_0                                                   (32'h510)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_1
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_1                                                   (32'h514)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_2
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_2                                                   (32'h518)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_3
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_3                                                   (32'h51c)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_4
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_4                                                   (32'h520)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_5
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_5                                                   (32'h524)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_6
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_6                                                   (32'h528)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_7
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_7                                                   (32'h52c)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_8
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_8                                                   (32'h530)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_9
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_9                                                   (32'h534)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_10
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_10                                                  (32'h538)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_11
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_11                                                  (32'h53c)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_0
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_0                                                   (32'h540)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_1
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_1                                                   (32'h544)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_2
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_2                                                   (32'h548)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_3
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_3                                                   (32'h54c)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_4
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_4                                                   (32'h550)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_5
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_5                                                   (32'h554)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_6
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_6                                                   (32'h558)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_7
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_7                                                   (32'h55c)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_8
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_8                                                   (32'h560)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_9
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_9                                                   (32'h564)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_10
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_10                                                  (32'h568)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_11
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_11                                                  (32'h56c)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_0
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_0                                                   (32'h570)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_1
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_1                                                   (32'h574)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_2
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_2                                                   (32'h578)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_3
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_3                                                   (32'h57c)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_4
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_4                                                   (32'h580)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_5
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_5                                                   (32'h584)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_6
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_6                                                   (32'h588)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_7
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_7                                                   (32'h58c)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_8
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_8                                                   (32'h590)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_9
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_9                                                   (32'h594)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_10
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_10                                                  (32'h598)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_11
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_11                                                  (32'h59c)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_0
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_0                                                   (32'h5a0)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_1
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_1                                                   (32'h5a4)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_2
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_2                                                   (32'h5a8)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_3
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_3                                                   (32'h5ac)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_4
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_4                                                   (32'h5b0)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_5
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_5                                                   (32'h5b4)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_6
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_6                                                   (32'h5b8)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_7
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_7                                                   (32'h5bc)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_8
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_8                                                   (32'h5c0)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_9
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_9                                                   (32'h5c4)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_10
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_10                                                  (32'h5c8)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_11
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_11                                                  (32'h5cc)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_0
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_0                                                   (32'h5d0)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_1
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_1                                                   (32'h5d4)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_2
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_2                                                   (32'h5d8)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_3
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_3                                                   (32'h5dc)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_4
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_4                                                   (32'h5e0)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_5
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_5                                                   (32'h5e4)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_6
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_6                                                   (32'h5e8)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_7
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_7                                                   (32'h5ec)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_8
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_8                                                   (32'h5f0)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_9
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_9                                                   (32'h5f4)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_10
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_10                                                  (32'h5f8)
`endif
`ifndef MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_11
`define MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_11                                                  (32'h5fc)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
`define MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                      (32'h1000)
`define MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                         (0)
`define MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                        (32'h1)
`define MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                         (1)
`define MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                        (32'h2)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R                                                      (32'h1004)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MCU_SRAM_DMI_AXI_COLLISION_EN_LOW              (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MCU_SRAM_DMI_AXI_COLLISION_EN_MASK             (32'h1)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_INTERNAL_EN_LOW                                (1)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_INTERNAL_EN_MASK                               (32'h2)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX0_INV_DEV_EN_LOW                           (2)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX0_INV_DEV_EN_MASK                          (32'h4)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX1_INV_DEV_EN_LOW                           (3)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX1_INV_DEV_EN_MASK                          (32'h8)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX0_CMD_FAIL_EN_LOW                          (4)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX0_CMD_FAIL_EN_MASK                         (32'h10)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX1_CMD_FAIL_EN_LOW                          (5)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX1_CMD_FAIL_EN_MASK                         (32'h20)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX0_ECC_UNC_EN_LOW                           (6)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX0_ECC_UNC_EN_MASK                          (32'h40)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX1_ECC_UNC_EN_LOW                           (7)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX1_ECC_UNC_EN_MASK                          (32'h80)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_LOW                      (8)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_MASK                     (32'h100)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_LOW                      (9)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_MASK                     (32'h200)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R                                                      (32'h1008)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL31_EN_LOW                       (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL31_EN_MASK                      (32'h1)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL30_EN_LOW                       (1)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL30_EN_MASK                      (32'h2)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL29_EN_LOW                       (2)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL29_EN_MASK                      (32'h4)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL28_EN_LOW                       (3)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL28_EN_MASK                      (32'h8)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL27_EN_LOW                       (4)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL27_EN_MASK                      (32'h10)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL26_EN_LOW                       (5)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL26_EN_MASK                      (32'h20)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL25_EN_LOW                       (6)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL25_EN_MASK                      (32'h40)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL24_EN_LOW                       (7)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL24_EN_MASK                      (32'h80)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL23_EN_LOW                       (8)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL23_EN_MASK                      (32'h100)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL22_EN_LOW                       (9)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL22_EN_MASK                      (32'h200)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL21_EN_LOW                       (10)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL21_EN_MASK                      (32'h400)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL20_EN_LOW                       (11)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL20_EN_MASK                      (32'h800)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL19_EN_LOW                       (12)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL19_EN_MASK                      (32'h1000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL18_EN_LOW                       (13)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL18_EN_MASK                      (32'h2000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL17_EN_LOW                       (14)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL17_EN_MASK                      (32'h4000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL16_EN_LOW                       (15)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL16_EN_MASK                      (32'h8000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL15_EN_LOW                       (16)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL15_EN_MASK                      (32'h10000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL14_EN_LOW                       (17)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL14_EN_MASK                      (32'h20000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL13_EN_LOW                       (18)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL13_EN_MASK                      (32'h40000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL12_EN_LOW                       (19)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL12_EN_MASK                      (32'h80000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL11_EN_LOW                       (20)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL11_EN_MASK                      (32'h100000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL10_EN_LOW                       (21)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL10_EN_MASK                      (32'h200000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL9_EN_LOW                        (22)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL9_EN_MASK                       (32'h400000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL8_EN_LOW                        (23)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL8_EN_MASK                       (32'h800000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL7_EN_LOW                        (24)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL7_EN_MASK                       (32'h1000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL6_EN_LOW                        (25)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL6_EN_MASK                       (32'h2000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL5_EN_LOW                        (26)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL5_EN_MASK                       (32'h4000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL4_EN_LOW                        (27)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL4_EN_MASK                       (32'h8000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL3_EN_LOW                        (28)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL3_EN_MASK                       (32'h10000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL2_EN_LOW                        (29)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL2_EN_MASK                       (32'h20000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL1_EN_LOW                        (30)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL1_EN_MASK                       (32'h40000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL0_EN_LOW                        (31)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL0_EN_MASK                       (32'h80000000)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R                                                      (32'h100c)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MCU_SRAM_ECC_COR_EN_LOW                        (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MCU_SRAM_ECC_COR_EN_MASK                       (32'h1)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_CPTRA_MCU_RESET_REQ_EN_LOW                     (1)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_CPTRA_MCU_RESET_REQ_EN_MASK                    (32'h2)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_GEN_IN_TOGGLE_EN_LOW                           (2)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_GEN_IN_TOGGLE_EN_MASK                          (32'h4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_CMD_AVAIL_EN_LOW                         (3)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_CMD_AVAIL_EN_MASK                        (32'h8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_CMD_AVAIL_EN_LOW                         (4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_CMD_AVAIL_EN_MASK                        (32'h10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_EN_LOW                    (5)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_EN_MASK                   (32'h20)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_ECC_COR_EN_LOW                           (6)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_ECC_COR_EN_MASK                          (32'h40)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_ECC_COR_EN_LOW                           (7)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_ECC_COR_EN_MASK                          (32'h80)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_DEBUG_LOCKED_EN_LOW                            (8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_DEBUG_LOCKED_EN_MASK                           (32'h100)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_SCAN_MODE_EN_LOW                               (9)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_SCAN_MODE_EN_MASK                              (32'h200)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_SOC_REQ_LOCK_EN_LOW                      (10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_SOC_REQ_LOCK_EN_MASK                     (32'h400)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_SOC_REQ_LOCK_EN_LOW                      (11)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_SOC_REQ_LOCK_EN_MASK                     (32'h800)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R                                                      (32'h1010)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL31_EN_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL31_EN_MASK                  (32'h1)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL30_EN_LOW                   (1)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL30_EN_MASK                  (32'h2)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL29_EN_LOW                   (2)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL29_EN_MASK                  (32'h4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL28_EN_LOW                   (3)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL28_EN_MASK                  (32'h8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL27_EN_LOW                   (4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL27_EN_MASK                  (32'h10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL26_EN_LOW                   (5)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL26_EN_MASK                  (32'h20)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL25_EN_LOW                   (6)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL25_EN_MASK                  (32'h40)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL24_EN_LOW                   (7)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL24_EN_MASK                  (32'h80)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL23_EN_LOW                   (8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL23_EN_MASK                  (32'h100)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL22_EN_LOW                   (9)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL22_EN_MASK                  (32'h200)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL21_EN_LOW                   (10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL21_EN_MASK                  (32'h400)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL20_EN_LOW                   (11)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL20_EN_MASK                  (32'h800)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL19_EN_LOW                   (12)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL19_EN_MASK                  (32'h1000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL18_EN_LOW                   (13)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL18_EN_MASK                  (32'h2000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL17_EN_LOW                   (14)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL17_EN_MASK                  (32'h4000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL16_EN_LOW                   (15)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL16_EN_MASK                  (32'h8000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL15_EN_LOW                   (16)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL15_EN_MASK                  (32'h10000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL14_EN_LOW                   (17)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL14_EN_MASK                  (32'h20000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL13_EN_LOW                   (18)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL13_EN_MASK                  (32'h40000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL12_EN_LOW                   (19)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL12_EN_MASK                  (32'h80000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL11_EN_LOW                   (20)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL11_EN_MASK                  (32'h100000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL10_EN_LOW                   (21)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL10_EN_MASK                  (32'h200000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL9_EN_LOW                    (22)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL9_EN_MASK                   (32'h400000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL8_EN_LOW                    (23)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL8_EN_MASK                   (32'h800000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL7_EN_LOW                    (24)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL7_EN_MASK                   (32'h1000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL6_EN_LOW                    (25)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL6_EN_MASK                   (32'h2000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL5_EN_LOW                    (26)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL5_EN_MASK                   (32'h4000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL4_EN_LOW                    (27)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL4_EN_MASK                   (32'h8000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL3_EN_LOW                    (28)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL3_EN_MASK                   (32'h10000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL2_EN_LOW                    (29)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL2_EN_MASK                   (32'h20000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL1_EN_LOW                    (30)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL1_EN_MASK                   (32'h40000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL0_EN_LOW                    (31)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL0_EN_MASK                   (32'h80000000)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                                   (32'h1014)
`define MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS0_LOW                                      (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS0_MASK                                     (32'h1)
`define MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS1_LOW                                      (1)
`define MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS1_MASK                                     (32'h2)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                                   (32'h1018)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS0_LOW                                      (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS0_MASK                                     (32'h1)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS1_LOW                                      (1)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS1_MASK                                     (32'h2)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R                                                (32'h101c)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MCU_SRAM_DMI_AXI_COLLISION_STS_LOW       (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MCU_SRAM_DMI_AXI_COLLISION_STS_MASK      (32'h1)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_INTERNAL_STS_LOW                         (1)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK                        (32'h2)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX0_INV_DEV_STS_LOW                    (2)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX0_INV_DEV_STS_MASK                   (32'h4)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX1_INV_DEV_STS_LOW                    (3)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX1_INV_DEV_STS_MASK                   (32'h8)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX0_CMD_FAIL_STS_LOW                   (4)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX0_CMD_FAIL_STS_MASK                  (32'h10)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX1_CMD_FAIL_STS_LOW                   (5)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX1_CMD_FAIL_STS_MASK                  (32'h20)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX0_ECC_UNC_STS_LOW                    (6)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX0_ECC_UNC_STS_MASK                   (32'h40)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX1_ECC_UNC_STS_LOW                    (7)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX1_ECC_UNC_STS_MASK                   (32'h80)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_LOW               (8)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK              (32'h100)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_LOW               (9)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_MASK              (32'h200)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R                                                (32'h1020)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL31_STS_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL31_STS_MASK               (32'h1)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL30_STS_LOW                (1)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL30_STS_MASK               (32'h2)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL29_STS_LOW                (2)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL29_STS_MASK               (32'h4)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL28_STS_LOW                (3)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL28_STS_MASK               (32'h8)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL27_STS_LOW                (4)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL27_STS_MASK               (32'h10)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL26_STS_LOW                (5)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL26_STS_MASK               (32'h20)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL25_STS_LOW                (6)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL25_STS_MASK               (32'h40)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL24_STS_LOW                (7)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL24_STS_MASK               (32'h80)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL23_STS_LOW                (8)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL23_STS_MASK               (32'h100)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL22_STS_LOW                (9)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL22_STS_MASK               (32'h200)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL21_STS_LOW                (10)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL21_STS_MASK               (32'h400)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL20_STS_LOW                (11)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL20_STS_MASK               (32'h800)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL19_STS_LOW                (12)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL19_STS_MASK               (32'h1000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL18_STS_LOW                (13)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL18_STS_MASK               (32'h2000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL17_STS_LOW                (14)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL17_STS_MASK               (32'h4000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL16_STS_LOW                (15)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL16_STS_MASK               (32'h8000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL15_STS_LOW                (16)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL15_STS_MASK               (32'h10000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL14_STS_LOW                (17)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL14_STS_MASK               (32'h20000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL13_STS_LOW                (18)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL13_STS_MASK               (32'h40000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL12_STS_LOW                (19)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL12_STS_MASK               (32'h80000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL11_STS_LOW                (20)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL11_STS_MASK               (32'h100000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL10_STS_LOW                (21)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL10_STS_MASK               (32'h200000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL9_STS_LOW                 (22)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL9_STS_MASK                (32'h400000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL8_STS_LOW                 (23)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL8_STS_MASK                (32'h800000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL7_STS_LOW                 (24)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL7_STS_MASK                (32'h1000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL6_STS_LOW                 (25)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL6_STS_MASK                (32'h2000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL5_STS_LOW                 (26)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL5_STS_MASK                (32'h4000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL4_STS_LOW                 (27)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL4_STS_MASK                (32'h8000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL3_STS_LOW                 (28)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL3_STS_MASK                (32'h10000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL2_STS_LOW                 (29)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL2_STS_MASK                (32'h20000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL1_STS_LOW                 (30)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL1_STS_MASK                (32'h40000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL0_STS_LOW                 (31)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_ERROR_AGG_ERROR_FATAL0_STS_MASK                (32'h80000000)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R                                                (32'h1024)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MCU_SRAM_ECC_COR_STS_LOW                 (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MCU_SRAM_ECC_COR_STS_MASK                (32'h1)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MCU_RESET_REQ_STS_LOW              (1)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MCU_RESET_REQ_STS_MASK             (32'h2)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_LOW                    (2)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK                   (32'h4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_CMD_AVAIL_STS_LOW                  (3)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_CMD_AVAIL_STS_MASK                 (32'h8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_CMD_AVAIL_STS_LOW                  (4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_CMD_AVAIL_STS_MASK                 (32'h10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_STS_LOW             (5)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_STS_MASK            (32'h20)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_ECC_COR_STS_LOW                    (6)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_ECC_COR_STS_MASK                   (32'h40)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_ECC_COR_STS_LOW                    (7)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_ECC_COR_STS_MASK                   (32'h80)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_LOW                     (8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK                    (32'h100)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_LOW                        (9)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_MASK                       (32'h200)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_SOC_REQ_LOCK_STS_LOW               (10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_SOC_REQ_LOCK_STS_MASK              (32'h400)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_SOC_REQ_LOCK_STS_LOW               (11)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_SOC_REQ_LOCK_STS_MASK              (32'h800)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R                                                (32'h1028)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL31_STS_LOW            (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL31_STS_MASK           (32'h1)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL30_STS_LOW            (1)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL30_STS_MASK           (32'h2)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL29_STS_LOW            (2)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL29_STS_MASK           (32'h4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL28_STS_LOW            (3)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL28_STS_MASK           (32'h8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL27_STS_LOW            (4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL27_STS_MASK           (32'h10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL26_STS_LOW            (5)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL26_STS_MASK           (32'h20)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL25_STS_LOW            (6)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL25_STS_MASK           (32'h40)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL24_STS_LOW            (7)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL24_STS_MASK           (32'h80)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL23_STS_LOW            (8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL23_STS_MASK           (32'h100)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL22_STS_LOW            (9)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL22_STS_MASK           (32'h200)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL21_STS_LOW            (10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL21_STS_MASK           (32'h400)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL20_STS_LOW            (11)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL20_STS_MASK           (32'h800)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL19_STS_LOW            (12)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL19_STS_MASK           (32'h1000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL18_STS_LOW            (13)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL18_STS_MASK           (32'h2000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL17_STS_LOW            (14)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL17_STS_MASK           (32'h4000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL16_STS_LOW            (15)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL16_STS_MASK           (32'h8000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL15_STS_LOW            (16)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL15_STS_MASK           (32'h10000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL14_STS_LOW            (17)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL14_STS_MASK           (32'h20000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL13_STS_LOW            (18)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL13_STS_MASK           (32'h40000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL12_STS_LOW            (19)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL12_STS_MASK           (32'h80000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL11_STS_LOW            (20)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL11_STS_MASK           (32'h100000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL10_STS_LOW            (21)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL10_STS_MASK           (32'h200000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL9_STS_LOW             (22)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL9_STS_MASK            (32'h400000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL8_STS_LOW             (23)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL8_STS_MASK            (32'h800000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL7_STS_LOW             (24)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL7_STS_MASK            (32'h1000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL6_STS_LOW             (25)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL6_STS_MASK            (32'h2000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL5_STS_LOW             (26)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL5_STS_MASK            (32'h4000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL4_STS_LOW             (27)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL4_STS_MASK            (32'h8000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL3_STS_LOW             (28)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL3_STS_MASK            (32'h10000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL2_STS_LOW             (29)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL2_STS_MASK            (32'h20000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL1_STS_LOW             (30)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL1_STS_MASK            (32'h40000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL0_STS_LOW             (31)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_NOTIF_AGG_ERROR_NON_FATAL0_STS_MASK            (32'h80000000)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R                                                    (32'h102c)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MCU_SRAM_DMI_AXI_COLLISION_TRIG_LOW          (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MCU_SRAM_DMI_AXI_COLLISION_TRIG_MASK         (32'h1)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_INTERNAL_TRIG_LOW                            (1)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_INTERNAL_TRIG_MASK                           (32'h2)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX0_INV_DEV_TRIG_LOW                       (2)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX0_INV_DEV_TRIG_MASK                      (32'h4)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX1_INV_DEV_TRIG_LOW                       (3)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX1_INV_DEV_TRIG_MASK                      (32'h8)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX0_CMD_FAIL_TRIG_LOW                      (4)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX0_CMD_FAIL_TRIG_MASK                     (32'h10)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX1_CMD_FAIL_TRIG_LOW                      (5)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX1_CMD_FAIL_TRIG_MASK                     (32'h20)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX0_ECC_UNC_TRIG_LOW                       (6)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX0_ECC_UNC_TRIG_MASK                      (32'h40)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX1_ECC_UNC_TRIG_LOW                       (7)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX1_ECC_UNC_TRIG_MASK                      (32'h80)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_WDT_TIMER1_TIMEOUT_TRIG_LOW                  (8)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_WDT_TIMER1_TIMEOUT_TRIG_MASK                 (32'h100)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_WDT_TIMER2_TIMEOUT_TRIG_LOW                  (9)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_WDT_TIMER2_TIMEOUT_TRIG_MASK                 (32'h200)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R                                                    (32'h1030)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL31_TRIG_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL31_TRIG_MASK                  (32'h1)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL30_TRIG_LOW                   (1)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL30_TRIG_MASK                  (32'h2)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL29_TRIG_LOW                   (2)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL29_TRIG_MASK                  (32'h4)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL28_TRIG_LOW                   (3)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL28_TRIG_MASK                  (32'h8)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL27_TRIG_LOW                   (4)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL27_TRIG_MASK                  (32'h10)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL26_TRIG_LOW                   (5)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL26_TRIG_MASK                  (32'h20)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL25_TRIG_LOW                   (6)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL25_TRIG_MASK                  (32'h40)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL24_TRIG_LOW                   (7)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL24_TRIG_MASK                  (32'h80)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL23_TRIG_LOW                   (8)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL23_TRIG_MASK                  (32'h100)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL22_TRIG_LOW                   (9)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL22_TRIG_MASK                  (32'h200)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL21_TRIG_LOW                   (10)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL21_TRIG_MASK                  (32'h400)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL20_TRIG_LOW                   (11)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL20_TRIG_MASK                  (32'h800)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL19_TRIG_LOW                   (12)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL19_TRIG_MASK                  (32'h1000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL18_TRIG_LOW                   (13)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL18_TRIG_MASK                  (32'h2000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL17_TRIG_LOW                   (14)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL17_TRIG_MASK                  (32'h4000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL16_TRIG_LOW                   (15)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL16_TRIG_MASK                  (32'h8000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL15_TRIG_LOW                   (16)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL15_TRIG_MASK                  (32'h10000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL14_TRIG_LOW                   (17)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL14_TRIG_MASK                  (32'h20000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL13_TRIG_LOW                   (18)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL13_TRIG_MASK                  (32'h40000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL12_TRIG_LOW                   (19)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL12_TRIG_MASK                  (32'h80000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL11_TRIG_LOW                   (20)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL11_TRIG_MASK                  (32'h100000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL10_TRIG_LOW                   (21)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL10_TRIG_MASK                  (32'h200000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL9_TRIG_LOW                    (22)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL9_TRIG_MASK                   (32'h400000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL8_TRIG_LOW                    (23)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL8_TRIG_MASK                   (32'h800000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL7_TRIG_LOW                    (24)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL7_TRIG_MASK                   (32'h1000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL6_TRIG_LOW                    (25)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL6_TRIG_MASK                   (32'h2000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL5_TRIG_LOW                    (26)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL5_TRIG_MASK                   (32'h4000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL4_TRIG_LOW                    (27)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL4_TRIG_MASK                   (32'h8000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL3_TRIG_LOW                    (28)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL3_TRIG_MASK                   (32'h10000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL2_TRIG_LOW                    (29)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL2_TRIG_MASK                   (32'h20000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL1_TRIG_LOW                    (30)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL1_TRIG_MASK                   (32'h40000000)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL0_TRIG_LOW                    (31)
`define MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL0_TRIG_MASK                   (32'h80000000)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R                                                    (32'h1034)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MCU_SRAM_ECC_COR_TRIG_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MCU_SRAM_ECC_COR_TRIG_MASK                   (32'h1)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_CPTRA_MCU_RESET_REQ_TRIG_LOW                 (1)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_CPTRA_MCU_RESET_REQ_TRIG_MASK                (32'h2)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_GEN_IN_TOGGLE_TRIG_LOW                       (2)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_GEN_IN_TOGGLE_TRIG_MASK                      (32'h4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_CMD_AVAIL_TRIG_LOW                     (3)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_CMD_AVAIL_TRIG_MASK                    (32'h8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_CMD_AVAIL_TRIG_LOW                     (4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_CMD_AVAIL_TRIG_MASK                    (32'h10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_TRIG_LOW                (5)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_TRIG_MASK               (32'h20)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_ECC_COR_TRIG_LOW                       (6)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_ECC_COR_TRIG_MASK                      (32'h40)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_ECC_COR_TRIG_LOW                       (7)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_ECC_COR_TRIG_MASK                      (32'h80)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_DEBUG_LOCKED_TRIG_LOW                        (8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_DEBUG_LOCKED_TRIG_MASK                       (32'h100)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_SCAN_MODE_TRIG_LOW                           (9)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_SCAN_MODE_TRIG_MASK                          (32'h200)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_SOC_REQ_LOCK_TRIG_LOW                  (10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_SOC_REQ_LOCK_TRIG_MASK                 (32'h400)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_SOC_REQ_LOCK_TRIG_LOW                  (11)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_SOC_REQ_LOCK_TRIG_MASK                 (32'h800)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R                                                    (32'h1038)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL31_TRIG_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL31_TRIG_MASK              (32'h1)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL30_TRIG_LOW               (1)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL30_TRIG_MASK              (32'h2)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL29_TRIG_LOW               (2)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL29_TRIG_MASK              (32'h4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL28_TRIG_LOW               (3)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL28_TRIG_MASK              (32'h8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL27_TRIG_LOW               (4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL27_TRIG_MASK              (32'h10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL26_TRIG_LOW               (5)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL26_TRIG_MASK              (32'h20)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL25_TRIG_LOW               (6)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL25_TRIG_MASK              (32'h40)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL24_TRIG_LOW               (7)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL24_TRIG_MASK              (32'h80)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL23_TRIG_LOW               (8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL23_TRIG_MASK              (32'h100)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL22_TRIG_LOW               (9)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL22_TRIG_MASK              (32'h200)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL21_TRIG_LOW               (10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL21_TRIG_MASK              (32'h400)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL20_TRIG_LOW               (11)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL20_TRIG_MASK              (32'h800)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL19_TRIG_LOW               (12)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL19_TRIG_MASK              (32'h1000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL18_TRIG_LOW               (13)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL18_TRIG_MASK              (32'h2000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL17_TRIG_LOW               (14)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL17_TRIG_MASK              (32'h4000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL16_TRIG_LOW               (15)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL16_TRIG_MASK              (32'h8000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL15_TRIG_LOW               (16)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL15_TRIG_MASK              (32'h10000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL14_TRIG_LOW               (17)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL14_TRIG_MASK              (32'h20000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL13_TRIG_LOW               (18)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL13_TRIG_MASK              (32'h40000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL12_TRIG_LOW               (19)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL12_TRIG_MASK              (32'h80000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL11_TRIG_LOW               (20)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL11_TRIG_MASK              (32'h100000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL10_TRIG_LOW               (21)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL10_TRIG_MASK              (32'h200000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL9_TRIG_LOW                (22)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL9_TRIG_MASK               (32'h400000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL8_TRIG_LOW                (23)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL8_TRIG_MASK               (32'h800000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL7_TRIG_LOW                (24)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL7_TRIG_MASK               (32'h1000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL6_TRIG_LOW                (25)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL6_TRIG_MASK               (32'h2000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL5_TRIG_LOW                (26)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL5_TRIG_MASK               (32'h4000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL4_TRIG_LOW                (27)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL4_TRIG_MASK               (32'h8000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL3_TRIG_LOW                (28)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL3_TRIG_MASK               (32'h10000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL2_TRIG_LOW                (29)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL2_TRIG_MASK               (32'h20000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL1_TRIG_LOW                (30)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL1_TRIG_MASK               (32'h40000000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL0_TRIG_LOW                (31)
`define MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL0_TRIG_MASK               (32'h80000000)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R                                           (32'h1100)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_INV_DEV_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_INV_DEV_INTR_COUNT_R                                      (32'h1104)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_INV_DEV_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_INV_DEV_INTR_COUNT_R                                      (32'h1108)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_CMD_FAIL_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_CMD_FAIL_INTR_COUNT_R                                     (32'h110c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_CMD_FAIL_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_CMD_FAIL_INTR_COUNT_R                                     (32'h1110)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R                                      (32'h1114)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R                                      (32'h1118)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R                         (32'h111c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R                                 (32'h1120)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R                                 (32'h1124)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R                                   (32'h1128)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R                                   (32'h112c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R                                   (32'h1130)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R                                   (32'h1134)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R                                   (32'h1138)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R                                   (32'h113c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R                                   (32'h1140)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R                                   (32'h1144)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R                                   (32'h1148)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R                                   (32'h114c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R                                  (32'h1150)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R                                  (32'h1154)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R                                  (32'h1158)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R                                  (32'h115c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R                                  (32'h1160)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R                                  (32'h1164)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R                                  (32'h1168)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R                                  (32'h116c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R                                  (32'h1170)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R                                  (32'h1174)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R                                  (32'h1178)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R                                  (32'h117c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R                                  (32'h1180)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R                                  (32'h1184)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R                                  (32'h1188)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R                                  (32'h118c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R                                  (32'h1190)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R                                  (32'h1194)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R                                  (32'h1198)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R                                  (32'h119c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R                                  (32'h11a0)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R                                  (32'h11a4)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R                                   (32'h1200)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R                                (32'h1204)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R                                      (32'h1208)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R                               (32'h120c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R                               (32'h1210)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R                               (32'h1214)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R                               (32'h1218)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R                               (32'h121c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R                               (32'h1220)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R                               (32'h1224)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R                               (32'h1228)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R                               (32'h122c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R                               (32'h1230)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R                              (32'h1234)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R                              (32'h1238)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R                              (32'h123c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R                              (32'h1240)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R                              (32'h1244)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R                              (32'h1248)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R                              (32'h124c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R                              (32'h1250)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R                              (32'h1254)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R                              (32'h1258)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R                              (32'h125c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R                              (32'h1260)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R                              (32'h1264)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R                              (32'h1268)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R                              (32'h126c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R                              (32'h1270)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R                              (32'h1274)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R                              (32'h1278)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R                              (32'h127c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R                              (32'h1280)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R                              (32'h1284)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R                              (32'h1288)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R                                    (32'h128c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R                                    (32'h1290)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R                               (32'h1294)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R                                      (32'h1298)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R                                      (32'h129c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R                                       (32'h12a0)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R                                          (32'h12a4)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R                                 (32'h12a8)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R                                 (32'h12ac)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R                                      (32'h1300)
`define MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_LOW                            (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_MASK                           (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_INV_DEV_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_INV_DEV_INTR_COUNT_INCR_R                                 (32'h1304)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_INV_DEV_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_INV_DEV_INTR_COUNT_INCR_R_PULSE_MASK                      (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_INV_DEV_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_INV_DEV_INTR_COUNT_INCR_R                                 (32'h1308)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_INV_DEV_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_INV_DEV_INTR_COUNT_INCR_R_PULSE_MASK                      (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_CMD_FAIL_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_CMD_FAIL_INTR_COUNT_INCR_R                                (32'h130c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_CMD_FAIL_INTR_COUNT_INCR_R_PULSE_LOW                      (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_CMD_FAIL_INTR_COUNT_INCR_R_PULSE_MASK                     (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_CMD_FAIL_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_CMD_FAIL_INTR_COUNT_INCR_R                                (32'h1310)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_CMD_FAIL_INTR_COUNT_INCR_R_PULSE_LOW                      (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_CMD_FAIL_INTR_COUNT_INCR_R_PULSE_MASK                     (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R                                 (32'h1314)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R_PULSE_MASK                      (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R                                 (32'h1318)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R_PULSE_MASK                      (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R                            (32'h131c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_PULSE_LOW                  (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_PULSE_MASK                 (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R                            (32'h1320)
`define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_PULSE_LOW                  (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_PULSE_MASK                 (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R                    (32'h1324)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R_PULSE_LOW          (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R_PULSE_MASK         (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R                              (32'h1328)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R                              (32'h132c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R                              (32'h1330)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R                              (32'h1334)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R                              (32'h1338)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R                              (32'h133c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R                              (32'h1340)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R                              (32'h1344)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R                              (32'h1348)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R                              (32'h134c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R                             (32'h1350)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R                             (32'h1354)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R                             (32'h1358)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R                             (32'h135c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R                             (32'h1360)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R                             (32'h1364)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R                             (32'h1368)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R                             (32'h136c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R                             (32'h1370)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R                             (32'h1374)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R                             (32'h1378)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R                             (32'h137c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R                             (32'h1380)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R                             (32'h1384)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R                             (32'h1388)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R                             (32'h138c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R                             (32'h1390)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R                             (32'h1394)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R                             (32'h1398)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R                             (32'h139c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R                             (32'h13a0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R                             (32'h13a4)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R                              (32'h13a8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R                           (32'h13ac)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R_PULSE_LOW                 (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R_PULSE_MASK                (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R                                 (32'h13b0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R_PULSE_MASK                      (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R                          (32'h13b4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R                          (32'h13b8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R                          (32'h13bc)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R                          (32'h13c0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R                          (32'h13c4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R                          (32'h13c8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R                          (32'h13cc)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R                          (32'h13d0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R                          (32'h13d4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R                          (32'h13d8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R                         (32'h13dc)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R                         (32'h13e0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R                         (32'h13e4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R                         (32'h13e8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R                         (32'h13ec)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R                         (32'h13f0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R                         (32'h13f4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R                         (32'h13f8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R                         (32'h13fc)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R                         (32'h1400)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R                         (32'h1404)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R                         (32'h1408)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R                         (32'h140c)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R                         (32'h1410)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R                         (32'h1414)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R                         (32'h1418)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R                         (32'h141c)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R                         (32'h1420)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R                         (32'h1424)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R                         (32'h1428)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R                         (32'h142c)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R                         (32'h1430)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R                               (32'h1434)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_LOW                     (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_MASK                    (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R                               (32'h1438)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_LOW                     (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_MASK                    (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R                          (32'h143c)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R                                 (32'h1440)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R_PULSE_MASK                      (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R                                 (32'h1444)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R_PULSE_MASK                      (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R                                  (32'h1448)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R_PULSE_LOW                        (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R_PULSE_MASK                       (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R                                     (32'h144c)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R_PULSE_LOW                           (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R_PULSE_MASK                          (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R                            (32'h1450)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R_PULSE_LOW                  (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R_PULSE_MASK                 (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R                            (32'h1454)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R_PULSE_LOW                  (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R_PULSE_MASK                 (32'h1)
`endif
`ifndef MCU_TRACE_BUFFER_CSR_STATUS
`define MCU_TRACE_BUFFER_CSR_STATUS                                                                 (32'h0)
`define MCU_TRACE_BUFFER_CSR_STATUS_WRAPPED_LOW                                                     (0)
`define MCU_TRACE_BUFFER_CSR_STATUS_WRAPPED_MASK                                                    (32'h1)
`define MCU_TRACE_BUFFER_CSR_STATUS_VALID_DATA_LOW                                                  (1)
`define MCU_TRACE_BUFFER_CSR_STATUS_VALID_DATA_MASK                                                 (32'h2)
`endif
`ifndef MCU_TRACE_BUFFER_CSR_CONFIG
`define MCU_TRACE_BUFFER_CSR_CONFIG                                                                 (32'h4)
`endif
`ifndef MCU_TRACE_BUFFER_CSR_DATA
`define MCU_TRACE_BUFFER_CSR_DATA                                                                   (32'h8)
`endif
`ifndef MCU_TRACE_BUFFER_CSR_WRITE_PTR
`define MCU_TRACE_BUFFER_CSR_WRITE_PTR                                                              (32'hc)
`endif
`ifndef MCU_TRACE_BUFFER_CSR_READ_PTR
`define MCU_TRACE_BUFFER_CSR_READ_PTR                                                               (32'h10)
`endif
`ifndef MBOX0_CSR_MBOX_LOCK
`define MBOX0_CSR_MBOX_LOCK                                                                         (32'h0)
`define MBOX0_CSR_MBOX_LOCK_LOCK_LOW                                                                (0)
`define MBOX0_CSR_MBOX_LOCK_LOCK_MASK                                                               (32'h1)
`endif
`ifndef MBOX0_CSR_MBOX_USER
`define MBOX0_CSR_MBOX_USER                                                                         (32'h4)
`endif
`ifndef MBOX0_CSR_MBOX_CMD
`define MBOX0_CSR_MBOX_CMD                                                                          (32'h8)
`endif
`ifndef MBOX0_CSR_MBOX_DLEN
`define MBOX0_CSR_MBOX_DLEN                                                                         (32'hc)
`endif
`ifndef MBOX0_CSR_MBOX_DATAIN
`define MBOX0_CSR_MBOX_DATAIN                                                                       (32'h10)
`endif
`ifndef MBOX0_CSR_MBOX_DATAOUT
`define MBOX0_CSR_MBOX_DATAOUT                                                                      (32'h14)
`endif
`ifndef MBOX0_CSR_MBOX_EXECUTE
`define MBOX0_CSR_MBOX_EXECUTE                                                                      (32'h18)
`define MBOX0_CSR_MBOX_EXECUTE_EXECUTE_LOW                                                          (0)
`define MBOX0_CSR_MBOX_EXECUTE_EXECUTE_MASK                                                         (32'h1)
`endif
`ifndef MBOX0_CSR_MBOX_STATUS
`define MBOX0_CSR_MBOX_STATUS                                                                       (32'h1c)
`define MBOX0_CSR_MBOX_STATUS_STATUS_LOW                                                            (0)
`define MBOX0_CSR_MBOX_STATUS_STATUS_MASK                                                           (32'hf)
`define MBOX0_CSR_MBOX_STATUS_ECC_SINGLE_ERROR_LOW                                                  (4)
`define MBOX0_CSR_MBOX_STATUS_ECC_SINGLE_ERROR_MASK                                                 (32'h10)
`define MBOX0_CSR_MBOX_STATUS_ECC_DOUBLE_ERROR_LOW                                                  (5)
`define MBOX0_CSR_MBOX_STATUS_ECC_DOUBLE_ERROR_MASK                                                 (32'h20)
`define MBOX0_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW                                                       (6)
`define MBOX0_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK                                                      (32'h1c0)
`define MBOX0_CSR_MBOX_STATUS_SOC_HAS_LOCK_LOW                                                      (9)
`define MBOX0_CSR_MBOX_STATUS_SOC_HAS_LOCK_MASK                                                     (32'h200)
`define MBOX0_CSR_MBOX_STATUS_MBOX_RDPTR_LOW                                                        (10)
`define MBOX0_CSR_MBOX_STATUS_MBOX_RDPTR_MASK                                                       (32'h3fffc00)
`endif
`ifndef MBOX0_CSR_MBOX_UNLOCK
`define MBOX0_CSR_MBOX_UNLOCK                                                                       (32'h20)
`define MBOX0_CSR_MBOX_UNLOCK_UNLOCK_LOW                                                            (0)
`define MBOX0_CSR_MBOX_UNLOCK_UNLOCK_MASK                                                           (32'h1)
`endif
`ifndef MBOX0_CSR_TAP_MODE
`define MBOX0_CSR_TAP_MODE                                                                          (32'h24)
`define MBOX0_CSR_TAP_MODE_ENABLED_LOW                                                              (0)
`define MBOX0_CSR_TAP_MODE_ENABLED_MASK                                                             (32'h1)
`endif
`ifndef MBOX1_CSR_MBOX_LOCK
`define MBOX1_CSR_MBOX_LOCK                                                                         (32'h0)
`define MBOX1_CSR_MBOX_LOCK_LOCK_LOW                                                                (0)
`define MBOX1_CSR_MBOX_LOCK_LOCK_MASK                                                               (32'h1)
`endif
`ifndef MBOX1_CSR_MBOX_USER
`define MBOX1_CSR_MBOX_USER                                                                         (32'h4)
`endif
`ifndef MBOX1_CSR_MBOX_CMD
`define MBOX1_CSR_MBOX_CMD                                                                          (32'h8)
`endif
`ifndef MBOX1_CSR_MBOX_DLEN
`define MBOX1_CSR_MBOX_DLEN                                                                         (32'hc)
`endif
`ifndef MBOX1_CSR_MBOX_DATAIN
`define MBOX1_CSR_MBOX_DATAIN                                                                       (32'h10)
`endif
`ifndef MBOX1_CSR_MBOX_DATAOUT
`define MBOX1_CSR_MBOX_DATAOUT                                                                      (32'h14)
`endif
`ifndef MBOX1_CSR_MBOX_EXECUTE
`define MBOX1_CSR_MBOX_EXECUTE                                                                      (32'h18)
`define MBOX1_CSR_MBOX_EXECUTE_EXECUTE_LOW                                                          (0)
`define MBOX1_CSR_MBOX_EXECUTE_EXECUTE_MASK                                                         (32'h1)
`endif
`ifndef MBOX1_CSR_MBOX_STATUS
`define MBOX1_CSR_MBOX_STATUS                                                                       (32'h1c)
`define MBOX1_CSR_MBOX_STATUS_STATUS_LOW                                                            (0)
`define MBOX1_CSR_MBOX_STATUS_STATUS_MASK                                                           (32'hf)
`define MBOX1_CSR_MBOX_STATUS_ECC_SINGLE_ERROR_LOW                                                  (4)
`define MBOX1_CSR_MBOX_STATUS_ECC_SINGLE_ERROR_MASK                                                 (32'h10)
`define MBOX1_CSR_MBOX_STATUS_ECC_DOUBLE_ERROR_LOW                                                  (5)
`define MBOX1_CSR_MBOX_STATUS_ECC_DOUBLE_ERROR_MASK                                                 (32'h20)
`define MBOX1_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW                                                       (6)
`define MBOX1_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK                                                      (32'h1c0)
`define MBOX1_CSR_MBOX_STATUS_SOC_HAS_LOCK_LOW                                                      (9)
`define MBOX1_CSR_MBOX_STATUS_SOC_HAS_LOCK_MASK                                                     (32'h200)
`define MBOX1_CSR_MBOX_STATUS_MBOX_RDPTR_LOW                                                        (10)
`define MBOX1_CSR_MBOX_STATUS_MBOX_RDPTR_MASK                                                       (32'h3fffc00)
`endif
`ifndef MBOX1_CSR_MBOX_UNLOCK
`define MBOX1_CSR_MBOX_UNLOCK                                                                       (32'h20)
`define MBOX1_CSR_MBOX_UNLOCK_UNLOCK_LOW                                                            (0)
`define MBOX1_CSR_MBOX_UNLOCK_UNLOCK_MASK                                                           (32'h1)
`endif
`ifndef MBOX1_CSR_TAP_MODE
`define MBOX1_CSR_TAP_MODE                                                                          (32'h24)
`define MBOX1_CSR_TAP_MODE_ENABLED_LOW                                                              (0)
`define MBOX1_CSR_TAP_MODE_ENABLED_MASK                                                             (32'h1)
`endif


`endif