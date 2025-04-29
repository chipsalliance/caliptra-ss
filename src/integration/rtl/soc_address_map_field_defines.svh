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
`ifndef SOC_ADDRESS_MAP_FIELD_DEFINES_HEADER
`define SOC_ADDRESS_MAP_FIELD_DEFINES_HEADER


`ifndef I3CCSR_I3CBASE_HCI_VERSION
`define I3CCSR_I3CBASE_HCI_VERSION                                                                  (32'h0)
`endif
`ifndef I3CCSR_I3CBASE_HC_CONTROL
`define I3CCSR_I3CBASE_HC_CONTROL                                                                   (32'h4)
`define I3CCSR_I3CBASE_HC_CONTROL_IBA_INCLUDE_LOW                                                   (0)
`define I3CCSR_I3CBASE_HC_CONTROL_IBA_INCLUDE_MASK                                                  (32'h1)
`define I3CCSR_I3CBASE_HC_CONTROL_AUTOCMD_DATA_RPT_LOW                                              (3)
`define I3CCSR_I3CBASE_HC_CONTROL_AUTOCMD_DATA_RPT_MASK                                             (32'h8)
`define I3CCSR_I3CBASE_HC_CONTROL_DATA_BYTE_ORDER_MODE_LOW                                          (4)
`define I3CCSR_I3CBASE_HC_CONTROL_DATA_BYTE_ORDER_MODE_MASK                                         (32'h10)
`define I3CCSR_I3CBASE_HC_CONTROL_MODE_SELECTOR_LOW                                                 (6)
`define I3CCSR_I3CBASE_HC_CONTROL_MODE_SELECTOR_MASK                                                (32'h40)
`define I3CCSR_I3CBASE_HC_CONTROL_I2C_DEV_PRESENT_LOW                                               (7)
`define I3CCSR_I3CBASE_HC_CONTROL_I2C_DEV_PRESENT_MASK                                              (32'h80)
`define I3CCSR_I3CBASE_HC_CONTROL_HOT_JOIN_CTRL_LOW                                                 (8)
`define I3CCSR_I3CBASE_HC_CONTROL_HOT_JOIN_CTRL_MASK                                                (32'h100)
`define I3CCSR_I3CBASE_HC_CONTROL_HALT_ON_CMD_SEQ_TIMEOUT_LOW                                       (12)
`define I3CCSR_I3CBASE_HC_CONTROL_HALT_ON_CMD_SEQ_TIMEOUT_MASK                                      (32'h1000)
`define I3CCSR_I3CBASE_HC_CONTROL_ABORT_LOW                                                         (29)
`define I3CCSR_I3CBASE_HC_CONTROL_ABORT_MASK                                                        (32'h20000000)
`define I3CCSR_I3CBASE_HC_CONTROL_RESUME_LOW                                                        (30)
`define I3CCSR_I3CBASE_HC_CONTROL_RESUME_MASK                                                       (32'h40000000)
`define I3CCSR_I3CBASE_HC_CONTROL_BUS_ENABLE_LOW                                                    (31)
`define I3CCSR_I3CBASE_HC_CONTROL_BUS_ENABLE_MASK                                                   (32'h80000000)
`endif
`ifndef I3CCSR_I3CBASE_CONTROLLER_DEVICE_ADDR
`define I3CCSR_I3CBASE_CONTROLLER_DEVICE_ADDR                                                       (32'h8)
`define I3CCSR_I3CBASE_CONTROLLER_DEVICE_ADDR_DYNAMIC_ADDR_LOW                                      (16)
`define I3CCSR_I3CBASE_CONTROLLER_DEVICE_ADDR_DYNAMIC_ADDR_MASK                                     (32'h7f0000)
`define I3CCSR_I3CBASE_CONTROLLER_DEVICE_ADDR_DYNAMIC_ADDR_VALID_LOW                                (31)
`define I3CCSR_I3CBASE_CONTROLLER_DEVICE_ADDR_DYNAMIC_ADDR_VALID_MASK                               (32'h80000000)
`endif
`ifndef I3CCSR_I3CBASE_HC_CAPABILITIES
`define I3CCSR_I3CBASE_HC_CAPABILITIES                                                              (32'hc)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_COMBO_COMMAND_LOW                                            (2)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_COMBO_COMMAND_MASK                                           (32'h4)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_AUTO_COMMAND_LOW                                             (3)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_AUTO_COMMAND_MASK                                            (32'h8)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_STANDBY_CR_CAP_LOW                                           (5)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_STANDBY_CR_CAP_MASK                                          (32'h20)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_HDR_DDR_EN_LOW                                               (6)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_HDR_DDR_EN_MASK                                              (32'h40)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_HDR_TS_EN_LOW                                                (7)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_HDR_TS_EN_MASK                                               (32'h80)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_CMD_CCC_DEFBYTE_LOW                                          (10)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_CMD_CCC_DEFBYTE_MASK                                         (32'h400)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_IBI_DATA_ABORT_EN_LOW                                        (11)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_IBI_DATA_ABORT_EN_MASK                                       (32'h800)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_IBI_CREDIT_COUNT_EN_LOW                                      (12)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_IBI_CREDIT_COUNT_EN_MASK                                     (32'h1000)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_SCHEDULED_COMMANDS_EN_LOW                                    (13)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_SCHEDULED_COMMANDS_EN_MASK                                   (32'h2000)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_CMD_SIZE_LOW                                                 (20)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_CMD_SIZE_MASK                                                (32'h300000)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_SG_CAPABILITY_CR_EN_LOW                                      (28)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_SG_CAPABILITY_CR_EN_MASK                                     (32'h10000000)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_SG_CAPABILITY_IBI_EN_LOW                                     (29)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_SG_CAPABILITY_IBI_EN_MASK                                    (32'h20000000)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_SG_CAPABILITY_DC_EN_LOW                                      (30)
`define I3CCSR_I3CBASE_HC_CAPABILITIES_SG_CAPABILITY_DC_EN_MASK                                     (32'h40000000)
`endif
`ifndef I3CCSR_I3CBASE_RESET_CONTROL
`define I3CCSR_I3CBASE_RESET_CONTROL                                                                (32'h10)
`define I3CCSR_I3CBASE_RESET_CONTROL_SOFT_RST_LOW                                                   (0)
`define I3CCSR_I3CBASE_RESET_CONTROL_SOFT_RST_MASK                                                  (32'h1)
`define I3CCSR_I3CBASE_RESET_CONTROL_CMD_QUEUE_RST_LOW                                              (1)
`define I3CCSR_I3CBASE_RESET_CONTROL_CMD_QUEUE_RST_MASK                                             (32'h2)
`define I3CCSR_I3CBASE_RESET_CONTROL_RESP_QUEUE_RST_LOW                                             (2)
`define I3CCSR_I3CBASE_RESET_CONTROL_RESP_QUEUE_RST_MASK                                            (32'h4)
`define I3CCSR_I3CBASE_RESET_CONTROL_TX_FIFO_RST_LOW                                                (3)
`define I3CCSR_I3CBASE_RESET_CONTROL_TX_FIFO_RST_MASK                                               (32'h8)
`define I3CCSR_I3CBASE_RESET_CONTROL_RX_FIFO_RST_LOW                                                (4)
`define I3CCSR_I3CBASE_RESET_CONTROL_RX_FIFO_RST_MASK                                               (32'h10)
`define I3CCSR_I3CBASE_RESET_CONTROL_IBI_QUEUE_RST_LOW                                              (5)
`define I3CCSR_I3CBASE_RESET_CONTROL_IBI_QUEUE_RST_MASK                                             (32'h20)
`endif
`ifndef I3CCSR_I3CBASE_PRESENT_STATE
`define I3CCSR_I3CBASE_PRESENT_STATE                                                                (32'h14)
`define I3CCSR_I3CBASE_PRESENT_STATE_AC_CURRENT_OWN_LOW                                             (2)
`define I3CCSR_I3CBASE_PRESENT_STATE_AC_CURRENT_OWN_MASK                                            (32'h4)
`endif
`ifndef I3CCSR_I3CBASE_INTR_STATUS
`define I3CCSR_I3CBASE_INTR_STATUS                                                                  (32'h20)
`define I3CCSR_I3CBASE_INTR_STATUS_HC_INTERNAL_ERR_STAT_LOW                                         (10)
`define I3CCSR_I3CBASE_INTR_STATUS_HC_INTERNAL_ERR_STAT_MASK                                        (32'h400)
`define I3CCSR_I3CBASE_INTR_STATUS_HC_SEQ_CANCEL_STAT_LOW                                           (11)
`define I3CCSR_I3CBASE_INTR_STATUS_HC_SEQ_CANCEL_STAT_MASK                                          (32'h800)
`define I3CCSR_I3CBASE_INTR_STATUS_HC_WARN_CMD_SEQ_STALL_STAT_LOW                                   (12)
`define I3CCSR_I3CBASE_INTR_STATUS_HC_WARN_CMD_SEQ_STALL_STAT_MASK                                  (32'h1000)
`define I3CCSR_I3CBASE_INTR_STATUS_HC_ERR_CMD_SEQ_TIMEOUT_STAT_LOW                                  (13)
`define I3CCSR_I3CBASE_INTR_STATUS_HC_ERR_CMD_SEQ_TIMEOUT_STAT_MASK                                 (32'h2000)
`define I3CCSR_I3CBASE_INTR_STATUS_SCHED_CMD_MISSED_TICK_STAT_LOW                                   (14)
`define I3CCSR_I3CBASE_INTR_STATUS_SCHED_CMD_MISSED_TICK_STAT_MASK                                  (32'h4000)
`endif
`ifndef I3CCSR_I3CBASE_INTR_STATUS_ENABLE
`define I3CCSR_I3CBASE_INTR_STATUS_ENABLE                                                           (32'h24)
`define I3CCSR_I3CBASE_INTR_STATUS_ENABLE_HC_INTERNAL_ERR_STAT_EN_LOW                               (10)
`define I3CCSR_I3CBASE_INTR_STATUS_ENABLE_HC_INTERNAL_ERR_STAT_EN_MASK                              (32'h400)
`define I3CCSR_I3CBASE_INTR_STATUS_ENABLE_HC_SEQ_CANCEL_STAT_EN_LOW                                 (11)
`define I3CCSR_I3CBASE_INTR_STATUS_ENABLE_HC_SEQ_CANCEL_STAT_EN_MASK                                (32'h800)
`define I3CCSR_I3CBASE_INTR_STATUS_ENABLE_HC_WARN_CMD_SEQ_STALL_STAT_EN_LOW                         (12)
`define I3CCSR_I3CBASE_INTR_STATUS_ENABLE_HC_WARN_CMD_SEQ_STALL_STAT_EN_MASK                        (32'h1000)
`define I3CCSR_I3CBASE_INTR_STATUS_ENABLE_HC_ERR_CMD_SEQ_TIMEOUT_STAT_EN_LOW                        (13)
`define I3CCSR_I3CBASE_INTR_STATUS_ENABLE_HC_ERR_CMD_SEQ_TIMEOUT_STAT_EN_MASK                       (32'h2000)
`define I3CCSR_I3CBASE_INTR_STATUS_ENABLE_SCHED_CMD_MISSED_TICK_STAT_EN_LOW                         (14)
`define I3CCSR_I3CBASE_INTR_STATUS_ENABLE_SCHED_CMD_MISSED_TICK_STAT_EN_MASK                        (32'h4000)
`endif
`ifndef I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE
`define I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE                                                           (32'h28)
`define I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE_HC_INTERNAL_ERR_SIGNAL_EN_LOW                             (10)
`define I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE_HC_INTERNAL_ERR_SIGNAL_EN_MASK                            (32'h400)
`define I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE_HC_SEQ_CANCEL_SIGNAL_EN_LOW                               (11)
`define I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE_HC_SEQ_CANCEL_SIGNAL_EN_MASK                              (32'h800)
`define I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE_HC_WARN_CMD_SEQ_STALL_SIGNAL_EN_LOW                       (12)
`define I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE_HC_WARN_CMD_SEQ_STALL_SIGNAL_EN_MASK                      (32'h1000)
`define I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE_HC_ERR_CMD_SEQ_TIMEOUT_SIGNAL_EN_LOW                      (13)
`define I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE_HC_ERR_CMD_SEQ_TIMEOUT_SIGNAL_EN_MASK                     (32'h2000)
`define I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE_SCHED_CMD_MISSED_TICK_SIGNAL_EN_LOW                       (14)
`define I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE_SCHED_CMD_MISSED_TICK_SIGNAL_EN_MASK                      (32'h4000)
`endif
`ifndef I3CCSR_I3CBASE_INTR_FORCE
`define I3CCSR_I3CBASE_INTR_FORCE                                                                   (32'h2c)
`define I3CCSR_I3CBASE_INTR_FORCE_HC_INTERNAL_ERR_FORCE_LOW                                         (10)
`define I3CCSR_I3CBASE_INTR_FORCE_HC_INTERNAL_ERR_FORCE_MASK                                        (32'h400)
`define I3CCSR_I3CBASE_INTR_FORCE_HC_SEQ_CANCEL_FORCE_LOW                                           (11)
`define I3CCSR_I3CBASE_INTR_FORCE_HC_SEQ_CANCEL_FORCE_MASK                                          (32'h800)
`define I3CCSR_I3CBASE_INTR_FORCE_HC_WARN_CMD_SEQ_STALL_FORCE_LOW                                   (12)
`define I3CCSR_I3CBASE_INTR_FORCE_HC_WARN_CMD_SEQ_STALL_FORCE_MASK                                  (32'h1000)
`define I3CCSR_I3CBASE_INTR_FORCE_HC_ERR_CMD_SEQ_TIMEOUT_FORCE_LOW                                  (13)
`define I3CCSR_I3CBASE_INTR_FORCE_HC_ERR_CMD_SEQ_TIMEOUT_FORCE_MASK                                 (32'h2000)
`define I3CCSR_I3CBASE_INTR_FORCE_SCHED_CMD_MISSED_TICK_FORCE_LOW                                   (14)
`define I3CCSR_I3CBASE_INTR_FORCE_SCHED_CMD_MISSED_TICK_FORCE_MASK                                  (32'h4000)
`endif
`ifndef I3CCSR_I3CBASE_DAT_SECTION_OFFSET
`define I3CCSR_I3CBASE_DAT_SECTION_OFFSET                                                           (32'h30)
`define I3CCSR_I3CBASE_DAT_SECTION_OFFSET_TABLE_OFFSET_LOW                                          (0)
`define I3CCSR_I3CBASE_DAT_SECTION_OFFSET_TABLE_OFFSET_MASK                                         (32'hfff)
`define I3CCSR_I3CBASE_DAT_SECTION_OFFSET_TABLE_SIZE_LOW                                            (12)
`define I3CCSR_I3CBASE_DAT_SECTION_OFFSET_TABLE_SIZE_MASK                                           (32'h7f000)
`define I3CCSR_I3CBASE_DAT_SECTION_OFFSET_ENTRY_SIZE_LOW                                            (28)
`define I3CCSR_I3CBASE_DAT_SECTION_OFFSET_ENTRY_SIZE_MASK                                           (32'hf0000000)
`endif
`ifndef I3CCSR_I3CBASE_DCT_SECTION_OFFSET
`define I3CCSR_I3CBASE_DCT_SECTION_OFFSET                                                           (32'h34)
`define I3CCSR_I3CBASE_DCT_SECTION_OFFSET_TABLE_OFFSET_LOW                                          (0)
`define I3CCSR_I3CBASE_DCT_SECTION_OFFSET_TABLE_OFFSET_MASK                                         (32'hfff)
`define I3CCSR_I3CBASE_DCT_SECTION_OFFSET_TABLE_SIZE_LOW                                            (12)
`define I3CCSR_I3CBASE_DCT_SECTION_OFFSET_TABLE_SIZE_MASK                                           (32'h7f000)
`define I3CCSR_I3CBASE_DCT_SECTION_OFFSET_TABLE_INDEX_LOW                                           (19)
`define I3CCSR_I3CBASE_DCT_SECTION_OFFSET_TABLE_INDEX_MASK                                          (32'hf80000)
`define I3CCSR_I3CBASE_DCT_SECTION_OFFSET_ENTRY_SIZE_LOW                                            (28)
`define I3CCSR_I3CBASE_DCT_SECTION_OFFSET_ENTRY_SIZE_MASK                                           (32'hf0000000)
`endif
`ifndef I3CCSR_I3CBASE_RING_HEADERS_SECTION_OFFSET
`define I3CCSR_I3CBASE_RING_HEADERS_SECTION_OFFSET                                                  (32'h38)
`define I3CCSR_I3CBASE_RING_HEADERS_SECTION_OFFSET_SECTION_OFFSET_LOW                               (0)
`define I3CCSR_I3CBASE_RING_HEADERS_SECTION_OFFSET_SECTION_OFFSET_MASK                              (32'hffff)
`endif
`ifndef I3CCSR_I3CBASE_PIO_SECTION_OFFSET
`define I3CCSR_I3CBASE_PIO_SECTION_OFFSET                                                           (32'h3c)
`define I3CCSR_I3CBASE_PIO_SECTION_OFFSET_SECTION_OFFSET_LOW                                        (0)
`define I3CCSR_I3CBASE_PIO_SECTION_OFFSET_SECTION_OFFSET_MASK                                       (32'hffff)
`endif
`ifndef I3CCSR_I3CBASE_EXT_CAPS_SECTION_OFFSET
`define I3CCSR_I3CBASE_EXT_CAPS_SECTION_OFFSET                                                      (32'h40)
`define I3CCSR_I3CBASE_EXT_CAPS_SECTION_OFFSET_SECTION_OFFSET_LOW                                   (0)
`define I3CCSR_I3CBASE_EXT_CAPS_SECTION_OFFSET_SECTION_OFFSET_MASK                                  (32'hffff)
`endif
`ifndef I3CCSR_I3CBASE_INT_CTRL_CMDS_EN
`define I3CCSR_I3CBASE_INT_CTRL_CMDS_EN                                                             (32'h4c)
`define I3CCSR_I3CBASE_INT_CTRL_CMDS_EN_ICC_SUPPORT_LOW                                             (0)
`define I3CCSR_I3CBASE_INT_CTRL_CMDS_EN_ICC_SUPPORT_MASK                                            (32'h1)
`define I3CCSR_I3CBASE_INT_CTRL_CMDS_EN_MIPI_CMDS_SUPPORTED_LOW                                     (1)
`define I3CCSR_I3CBASE_INT_CTRL_CMDS_EN_MIPI_CMDS_SUPPORTED_MASK                                    (32'hfffe)
`endif
`ifndef I3CCSR_I3CBASE_IBI_NOTIFY_CTRL
`define I3CCSR_I3CBASE_IBI_NOTIFY_CTRL                                                              (32'h58)
`define I3CCSR_I3CBASE_IBI_NOTIFY_CTRL_NOTIFY_HJ_REJECTED_LOW                                       (0)
`define I3CCSR_I3CBASE_IBI_NOTIFY_CTRL_NOTIFY_HJ_REJECTED_MASK                                      (32'h1)
`define I3CCSR_I3CBASE_IBI_NOTIFY_CTRL_NOTIFY_CRR_REJECTED_LOW                                      (1)
`define I3CCSR_I3CBASE_IBI_NOTIFY_CTRL_NOTIFY_CRR_REJECTED_MASK                                     (32'h2)
`define I3CCSR_I3CBASE_IBI_NOTIFY_CTRL_NOTIFY_IBI_REJECTED_LOW                                      (3)
`define I3CCSR_I3CBASE_IBI_NOTIFY_CTRL_NOTIFY_IBI_REJECTED_MASK                                     (32'h8)
`endif
`ifndef I3CCSR_I3CBASE_IBI_DATA_ABORT_CTRL
`define I3CCSR_I3CBASE_IBI_DATA_ABORT_CTRL                                                          (32'h5c)
`define I3CCSR_I3CBASE_IBI_DATA_ABORT_CTRL_MATCH_IBI_ID_LOW                                         (8)
`define I3CCSR_I3CBASE_IBI_DATA_ABORT_CTRL_MATCH_IBI_ID_MASK                                        (32'hff00)
`define I3CCSR_I3CBASE_IBI_DATA_ABORT_CTRL_AFTER_N_CHUNKS_LOW                                       (16)
`define I3CCSR_I3CBASE_IBI_DATA_ABORT_CTRL_AFTER_N_CHUNKS_MASK                                      (32'h30000)
`define I3CCSR_I3CBASE_IBI_DATA_ABORT_CTRL_MATCH_STATUS_TYPE_LOW                                    (18)
`define I3CCSR_I3CBASE_IBI_DATA_ABORT_CTRL_MATCH_STATUS_TYPE_MASK                                   (32'h1c0000)
`define I3CCSR_I3CBASE_IBI_DATA_ABORT_CTRL_IBI_DATA_ABORT_MON_LOW                                   (31)
`define I3CCSR_I3CBASE_IBI_DATA_ABORT_CTRL_IBI_DATA_ABORT_MON_MASK                                  (32'h80000000)
`endif
`ifndef I3CCSR_I3CBASE_DEV_CTX_BASE_LO
`define I3CCSR_I3CBASE_DEV_CTX_BASE_LO                                                              (32'h60)
`define I3CCSR_I3CBASE_DEV_CTX_BASE_LO_BASE_LO_LOW                                                  (0)
`define I3CCSR_I3CBASE_DEV_CTX_BASE_LO_BASE_LO_MASK                                                 (32'h1)
`endif
`ifndef I3CCSR_I3CBASE_DEV_CTX_BASE_HI
`define I3CCSR_I3CBASE_DEV_CTX_BASE_HI                                                              (32'h64)
`define I3CCSR_I3CBASE_DEV_CTX_BASE_HI_BASE_HI_LOW                                                  (0)
`define I3CCSR_I3CBASE_DEV_CTX_BASE_HI_BASE_HI_MASK                                                 (32'h1)
`endif
`ifndef I3CCSR_I3CBASE_DEV_CTX_SG
`define I3CCSR_I3CBASE_DEV_CTX_SG                                                                   (32'h68)
`define I3CCSR_I3CBASE_DEV_CTX_SG_LIST_SIZE_LOW                                                     (0)
`define I3CCSR_I3CBASE_DEV_CTX_SG_LIST_SIZE_MASK                                                    (32'hffff)
`define I3CCSR_I3CBASE_DEV_CTX_SG_BLP_LOW                                                           (31)
`define I3CCSR_I3CBASE_DEV_CTX_SG_BLP_MASK                                                          (32'h80000000)
`endif
`ifndef I3CCSR_PIOCONTROL_COMMAND_PORT
`define I3CCSR_PIOCONTROL_COMMAND_PORT                                                              (32'h80)
`endif
`ifndef I3CCSR_PIOCONTROL_RESPONSE_PORT
`define I3CCSR_PIOCONTROL_RESPONSE_PORT                                                             (32'h84)
`endif
`ifndef I3CCSR_PIOCONTROL_TX_DATA_PORT
`define I3CCSR_PIOCONTROL_TX_DATA_PORT                                                              (32'h88)
`endif
`ifndef I3CCSR_PIOCONTROL_RX_DATA_PORT
`define I3CCSR_PIOCONTROL_RX_DATA_PORT                                                              (32'h88)
`endif
`ifndef I3CCSR_PIOCONTROL_IBI_PORT
`define I3CCSR_PIOCONTROL_IBI_PORT                                                                  (32'h8c)
`endif
`ifndef I3CCSR_PIOCONTROL_QUEUE_THLD_CTRL
`define I3CCSR_PIOCONTROL_QUEUE_THLD_CTRL                                                           (32'h90)
`define I3CCSR_PIOCONTROL_QUEUE_THLD_CTRL_CMD_EMPTY_BUF_THLD_LOW                                    (0)
`define I3CCSR_PIOCONTROL_QUEUE_THLD_CTRL_CMD_EMPTY_BUF_THLD_MASK                                   (32'hff)
`define I3CCSR_PIOCONTROL_QUEUE_THLD_CTRL_RESP_BUF_THLD_LOW                                         (8)
`define I3CCSR_PIOCONTROL_QUEUE_THLD_CTRL_RESP_BUF_THLD_MASK                                        (32'hff00)
`define I3CCSR_PIOCONTROL_QUEUE_THLD_CTRL_IBI_DATA_SEGMENT_SIZE_LOW                                 (16)
`define I3CCSR_PIOCONTROL_QUEUE_THLD_CTRL_IBI_DATA_SEGMENT_SIZE_MASK                                (32'hff0000)
`define I3CCSR_PIOCONTROL_QUEUE_THLD_CTRL_IBI_STATUS_THLD_LOW                                       (24)
`define I3CCSR_PIOCONTROL_QUEUE_THLD_CTRL_IBI_STATUS_THLD_MASK                                      (32'hff000000)
`endif
`ifndef I3CCSR_PIOCONTROL_DATA_BUFFER_THLD_CTRL
`define I3CCSR_PIOCONTROL_DATA_BUFFER_THLD_CTRL                                                     (32'h94)
`define I3CCSR_PIOCONTROL_DATA_BUFFER_THLD_CTRL_TX_BUF_THLD_LOW                                     (0)
`define I3CCSR_PIOCONTROL_DATA_BUFFER_THLD_CTRL_TX_BUF_THLD_MASK                                    (32'h7)
`define I3CCSR_PIOCONTROL_DATA_BUFFER_THLD_CTRL_RX_BUF_THLD_LOW                                     (8)
`define I3CCSR_PIOCONTROL_DATA_BUFFER_THLD_CTRL_RX_BUF_THLD_MASK                                    (32'h700)
`define I3CCSR_PIOCONTROL_DATA_BUFFER_THLD_CTRL_TX_START_THLD_LOW                                   (16)
`define I3CCSR_PIOCONTROL_DATA_BUFFER_THLD_CTRL_TX_START_THLD_MASK                                  (32'h70000)
`define I3CCSR_PIOCONTROL_DATA_BUFFER_THLD_CTRL_RX_START_THLD_LOW                                   (24)
`define I3CCSR_PIOCONTROL_DATA_BUFFER_THLD_CTRL_RX_START_THLD_MASK                                  (32'h7000000)
`endif
`ifndef I3CCSR_PIOCONTROL_QUEUE_SIZE
`define I3CCSR_PIOCONTROL_QUEUE_SIZE                                                                (32'h98)
`define I3CCSR_PIOCONTROL_QUEUE_SIZE_CR_QUEUE_SIZE_LOW                                              (0)
`define I3CCSR_PIOCONTROL_QUEUE_SIZE_CR_QUEUE_SIZE_MASK                                             (32'hff)
`define I3CCSR_PIOCONTROL_QUEUE_SIZE_IBI_STATUS_SIZE_LOW                                            (8)
`define I3CCSR_PIOCONTROL_QUEUE_SIZE_IBI_STATUS_SIZE_MASK                                           (32'hff00)
`define I3CCSR_PIOCONTROL_QUEUE_SIZE_RX_DATA_BUFFER_SIZE_LOW                                        (16)
`define I3CCSR_PIOCONTROL_QUEUE_SIZE_RX_DATA_BUFFER_SIZE_MASK                                       (32'hff0000)
`define I3CCSR_PIOCONTROL_QUEUE_SIZE_TX_DATA_BUFFER_SIZE_LOW                                        (24)
`define I3CCSR_PIOCONTROL_QUEUE_SIZE_TX_DATA_BUFFER_SIZE_MASK                                       (32'hff000000)
`endif
`ifndef I3CCSR_PIOCONTROL_ALT_QUEUE_SIZE
`define I3CCSR_PIOCONTROL_ALT_QUEUE_SIZE                                                            (32'h9c)
`define I3CCSR_PIOCONTROL_ALT_QUEUE_SIZE_ALT_RESP_QUEUE_SIZE_LOW                                    (0)
`define I3CCSR_PIOCONTROL_ALT_QUEUE_SIZE_ALT_RESP_QUEUE_SIZE_MASK                                   (32'hff)
`define I3CCSR_PIOCONTROL_ALT_QUEUE_SIZE_ALT_RESP_QUEUE_EN_LOW                                      (24)
`define I3CCSR_PIOCONTROL_ALT_QUEUE_SIZE_ALT_RESP_QUEUE_EN_MASK                                     (32'h1000000)
`define I3CCSR_PIOCONTROL_ALT_QUEUE_SIZE_EXT_IBI_QUEUE_EN_LOW                                       (28)
`define I3CCSR_PIOCONTROL_ALT_QUEUE_SIZE_EXT_IBI_QUEUE_EN_MASK                                      (32'h10000000)
`endif
`ifndef I3CCSR_PIOCONTROL_PIO_INTR_STATUS
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS                                                           (32'ha0)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_TX_THLD_STAT_LOW                                          (0)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_TX_THLD_STAT_MASK                                         (32'h1)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_RX_THLD_STAT_LOW                                          (1)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_RX_THLD_STAT_MASK                                         (32'h2)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_IBI_STATUS_THLD_STAT_LOW                                  (2)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_IBI_STATUS_THLD_STAT_MASK                                 (32'h4)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_CMD_QUEUE_READY_STAT_LOW                                  (3)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_CMD_QUEUE_READY_STAT_MASK                                 (32'h8)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_RESP_READY_STAT_LOW                                       (4)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_RESP_READY_STAT_MASK                                      (32'h10)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_TRANSFER_ABORT_STAT_LOW                                   (5)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_TRANSFER_ABORT_STAT_MASK                                  (32'h20)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_TRANSFER_ERR_STAT_LOW                                     (9)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_TRANSFER_ERR_STAT_MASK                                    (32'h200)
`endif
`ifndef I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE                                                    (32'ha4)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_TX_THLD_STAT_EN_LOW                                (0)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_TX_THLD_STAT_EN_MASK                               (32'h1)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_RX_THLD_STAT_EN_LOW                                (1)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_RX_THLD_STAT_EN_MASK                               (32'h2)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_IBI_STATUS_THLD_STAT_EN_LOW                        (2)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_IBI_STATUS_THLD_STAT_EN_MASK                       (32'h4)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_CMD_QUEUE_READY_STAT_EN_LOW                        (3)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_CMD_QUEUE_READY_STAT_EN_MASK                       (32'h8)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_RESP_READY_STAT_EN_LOW                             (4)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_RESP_READY_STAT_EN_MASK                            (32'h10)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_TRANSFER_ABORT_STAT_EN_LOW                         (5)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_TRANSFER_ABORT_STAT_EN_MASK                        (32'h20)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_TRANSFER_ERR_STAT_EN_LOW                           (9)
`define I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_TRANSFER_ERR_STAT_EN_MASK                          (32'h200)
`endif
`ifndef I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE
`define I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE                                                    (32'ha8)
`define I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_TX_THLD_SIGNAL_EN_LOW                              (0)
`define I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_TX_THLD_SIGNAL_EN_MASK                             (32'h1)
`define I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_RX_THLD_SIGNAL_EN_LOW                              (1)
`define I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_RX_THLD_SIGNAL_EN_MASK                             (32'h2)
`define I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_IBI_STATUS_THLD_SIGNAL_EN_LOW                      (2)
`define I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_IBI_STATUS_THLD_SIGNAL_EN_MASK                     (32'h4)
`define I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_CMD_QUEUE_READY_SIGNAL_EN_LOW                      (3)
`define I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_CMD_QUEUE_READY_SIGNAL_EN_MASK                     (32'h8)
`define I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_RESP_READY_SIGNAL_EN_LOW                           (4)
`define I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_RESP_READY_SIGNAL_EN_MASK                          (32'h10)
`define I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_TRANSFER_ABORT_SIGNAL_EN_LOW                       (5)
`define I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_TRANSFER_ABORT_SIGNAL_EN_MASK                      (32'h20)
`define I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_TRANSFER_ERR_SIGNAL_EN_LOW                         (9)
`define I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_TRANSFER_ERR_SIGNAL_EN_MASK                        (32'h200)
`endif
`ifndef I3CCSR_PIOCONTROL_PIO_INTR_FORCE
`define I3CCSR_PIOCONTROL_PIO_INTR_FORCE                                                            (32'hac)
`define I3CCSR_PIOCONTROL_PIO_INTR_FORCE_TX_THLD_FORCE_LOW                                          (0)
`define I3CCSR_PIOCONTROL_PIO_INTR_FORCE_TX_THLD_FORCE_MASK                                         (32'h1)
`define I3CCSR_PIOCONTROL_PIO_INTR_FORCE_RX_THLD_FORCE_LOW                                          (1)
`define I3CCSR_PIOCONTROL_PIO_INTR_FORCE_RX_THLD_FORCE_MASK                                         (32'h2)
`define I3CCSR_PIOCONTROL_PIO_INTR_FORCE_IBI_THLD_FORCE_LOW                                         (2)
`define I3CCSR_PIOCONTROL_PIO_INTR_FORCE_IBI_THLD_FORCE_MASK                                        (32'h4)
`define I3CCSR_PIOCONTROL_PIO_INTR_FORCE_CMD_QUEUE_READY_FORCE_LOW                                  (3)
`define I3CCSR_PIOCONTROL_PIO_INTR_FORCE_CMD_QUEUE_READY_FORCE_MASK                                 (32'h8)
`define I3CCSR_PIOCONTROL_PIO_INTR_FORCE_RESP_READY_FORCE_LOW                                       (4)
`define I3CCSR_PIOCONTROL_PIO_INTR_FORCE_RESP_READY_FORCE_MASK                                      (32'h10)
`define I3CCSR_PIOCONTROL_PIO_INTR_FORCE_TRANSFER_ABORT_FORCE_LOW                                   (5)
`define I3CCSR_PIOCONTROL_PIO_INTR_FORCE_TRANSFER_ABORT_FORCE_MASK                                  (32'h20)
`define I3CCSR_PIOCONTROL_PIO_INTR_FORCE_TRANSFER_ERR_FORCE_LOW                                     (9)
`define I3CCSR_PIOCONTROL_PIO_INTR_FORCE_TRANSFER_ERR_FORCE_MASK                                    (32'h200)
`endif
`ifndef I3CCSR_PIOCONTROL_PIO_CONTROL
`define I3CCSR_PIOCONTROL_PIO_CONTROL                                                               (32'hb0)
`define I3CCSR_PIOCONTROL_PIO_CONTROL_ENABLE_LOW                                                    (0)
`define I3CCSR_PIOCONTROL_PIO_CONTROL_ENABLE_MASK                                                   (32'h1)
`define I3CCSR_PIOCONTROL_PIO_CONTROL_RS_LOW                                                        (1)
`define I3CCSR_PIOCONTROL_PIO_CONTROL_RS_MASK                                                       (32'h2)
`define I3CCSR_PIOCONTROL_PIO_CONTROL_ABORT_LOW                                                     (2)
`define I3CCSR_PIOCONTROL_PIO_CONTROL_ABORT_MASK                                                    (32'h4)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_EXTCAP_HEADER
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_EXTCAP_HEADER                                                 (32'h0)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_EXTCAP_HEADER_CAP_ID_LOW                                      (0)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_EXTCAP_HEADER_CAP_ID_MASK                                     (32'hff)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_EXTCAP_HEADER_CAP_LENGTH_LOW                                  (8)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_EXTCAP_HEADER_CAP_LENGTH_MASK                                 (32'hffff00)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_0
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_0                                                    (32'h4)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_1
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_1                                                    (32'h8)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_2
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_2                                                    (32'hc)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_2_REC_PROT_VERSION_LOW                               (0)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_2_REC_PROT_VERSION_MASK                              (32'hffff)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_2_AGENT_CAPS_LOW                                     (16)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_2_AGENT_CAPS_MASK                                    (32'hffff0000)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_3
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_3                                                    (32'h10)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_3_NUM_OF_CMS_REGIONS_LOW                             (0)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_3_NUM_OF_CMS_REGIONS_MASK                            (32'hff)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_3_MAX_RESP_TIME_LOW                                  (8)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_3_MAX_RESP_TIME_MASK                                 (32'hff00)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_3_HEARTBEAT_PERIOD_LOW                               (16)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_3_HEARTBEAT_PERIOD_MASK                              (32'hff0000)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_0
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_0                                                   (32'h14)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_0_DESC_TYPE_LOW                                     (0)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_0_DESC_TYPE_MASK                                    (32'hff)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_0_VENDOR_SPECIFIC_STR_LENGTH_LOW                    (8)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_0_VENDOR_SPECIFIC_STR_LENGTH_MASK                   (32'hff00)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_0_DATA_LOW                                          (16)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_0_DATA_MASK                                         (32'hffff0000)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_1
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_1                                                   (32'h18)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_2
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_2                                                   (32'h1c)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_3
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_3                                                   (32'h20)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_4
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_4                                                   (32'h24)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_5
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_5                                                   (32'h28)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_RESERVED
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_RESERVED                                            (32'h2c)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0                                               (32'h30)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0_DEV_STATUS_LOW                                (0)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0_DEV_STATUS_MASK                               (32'hff)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0_PROT_ERROR_LOW                                (8)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0_PROT_ERROR_MASK                               (32'hff00)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0_REC_REASON_CODE_LOW                           (16)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0_REC_REASON_CODE_MASK                          (32'hffff0000)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_1
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_1                                               (32'h34)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_1_HEARTBEAT_LOW                                 (0)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_1_HEARTBEAT_MASK                                (32'hffff)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_1_VENDOR_STATUS_LENGTH_LOW                      (16)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_1_VENDOR_STATUS_LENGTH_MASK                     (32'h1ff0000)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_1_VENDOR_STATUS_LOW                             (25)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_1_VENDOR_STATUS_MASK                            (32'hfe000000)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_RESET
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_RESET                                                  (32'h38)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_RESET_RESET_CTRL_LOW                                   (0)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_RESET_RESET_CTRL_MASK                                  (32'hff)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_RESET_FORCED_RECOVERY_LOW                              (8)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_RESET_FORCED_RECOVERY_MASK                             (32'hff00)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_RESET_IF_CTRL_LOW                                      (16)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_RESET_IF_CTRL_MASK                                     (32'hff0000)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL                                                 (32'h3c)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL_CMS_LOW                                         (0)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL_CMS_MASK                                        (32'hff)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL_REC_IMG_SEL_LOW                                 (8)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL_REC_IMG_SEL_MASK                                (32'hff00)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL_ACTIVATE_REC_IMG_LOW                            (16)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL_ACTIVATE_REC_IMG_MASK                           (32'hff0000)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS                                               (32'h40)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS_DEV_REC_STATUS_LOW                            (0)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS_DEV_REC_STATUS_MASK                           (32'hf)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS_REC_IMG_INDEX_LOW                             (4)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS_REC_IMG_INDEX_MASK                            (32'hf0)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS_VENDOR_SPECIFIC_STATUS_LOW                    (8)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS_VENDOR_SPECIFIC_STATUS_MASK                   (32'hff00)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS                                                     (32'h44)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS_TEMP_CRITICAL_LOW                                   (0)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS_TEMP_CRITICAL_MASK                                  (32'h1)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS_SOFT_ERR_LOW                                        (1)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS_SOFT_ERR_MASK                                       (32'h2)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS_FATAL_ERR_LOW                                       (2)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS_FATAL_ERR_MASK                                      (32'h4)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS_RESERVED_7_3_LOW                                    (3)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS_RESERVED_7_3_MASK                                   (32'hf8)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS_VENDOR_HW_STATUS_LOW                                (8)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS_VENDOR_HW_STATUS_MASK                               (32'hff00)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS_CTEMP_LOW                                           (16)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS_CTEMP_MASK                                          (32'hff0000)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS_VENDOR_HW_STATUS_LEN_LOW                            (24)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS_VENDOR_HW_STATUS_LEN_MASK                           (32'hff000000)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_0
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_0                                          (32'h48)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_0_CMS_LOW                                  (0)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_0_CMS_MASK                                 (32'hff)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_0_RESET_LOW                                (8)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_0_RESET_MASK                               (32'hff00)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_1
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_1                                          (32'h4c)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_0
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_0                                        (32'h50)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_0_EMPTY_LOW                              (0)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_0_EMPTY_MASK                             (32'h1)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_0_FULL_LOW                               (1)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_0_FULL_MASK                              (32'h2)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_0_REGION_TYPE_LOW                        (8)
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_0_REGION_TYPE_MASK                       (32'h700)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_1
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_1                                        (32'h54)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_2
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_2                                        (32'h58)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_3
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_3                                        (32'h5c)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_4
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_4                                        (32'h60)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_RESERVED
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_RESERVED                                        (32'h64)
`endif
`ifndef I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_DATA
`define I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_DATA                                            (32'h68)
`endif
`ifndef I3CCSR_I3C_EC_STDBYCTRLMODE_EXTCAP_HEADER
`define I3CCSR_I3C_EC_STDBYCTRLMODE_EXTCAP_HEADER                                                   (32'h80)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_EXTCAP_HEADER_CAP_ID_LOW                                        (0)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_EXTCAP_HEADER_CAP_ID_MASK                                       (32'hff)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_EXTCAP_HEADER_CAP_LENGTH_LOW                                    (8)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_EXTCAP_HEADER_CAP_LENGTH_MASK                                   (32'hffff00)
`endif
`ifndef I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL                                                 (32'h84)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_PENDING_RX_NACK_LOW                             (0)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_PENDING_RX_NACK_MASK                            (32'h1)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_HANDOFF_DELAY_NACK_LOW                          (1)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_HANDOFF_DELAY_NACK_MASK                         (32'h2)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_ACR_FSM_OP_SELECT_LOW                           (2)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_ACR_FSM_OP_SELECT_MASK                          (32'h4)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_PRIME_ACCEPT_GETACCCR_LOW                       (3)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_PRIME_ACCEPT_GETACCCR_MASK                      (32'h8)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_HANDOFF_DEEP_SLEEP_LOW                          (4)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_HANDOFF_DEEP_SLEEP_MASK                         (32'h10)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_CR_REQUEST_SEND_LOW                             (5)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_CR_REQUEST_SEND_MASK                            (32'h20)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_BAST_CCC_IBI_RING_LOW                           (8)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_BAST_CCC_IBI_RING_MASK                          (32'h700)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_TARGET_XACT_ENABLE_LOW                          (12)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_TARGET_XACT_ENABLE_MASK                         (32'h1000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_DAA_SETAASA_ENABLE_LOW                          (13)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_DAA_SETAASA_ENABLE_MASK                         (32'h2000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_DAA_SETDASA_ENABLE_LOW                          (14)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_DAA_SETDASA_ENABLE_MASK                         (32'h4000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_DAA_ENTDAA_ENABLE_LOW                           (15)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_DAA_ENTDAA_ENABLE_MASK                          (32'h8000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_RSTACT_DEFBYTE_02_LOW                           (20)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_RSTACT_DEFBYTE_02_MASK                          (32'h100000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_STBY_CR_ENABLE_INIT_LOW                         (30)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_STBY_CR_ENABLE_INIT_MASK                        (32'hc0000000)
`endif
`ifndef I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_ADDR
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_ADDR                                             (32'h88)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_ADDR_STATIC_ADDR_LOW                             (0)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_ADDR_STATIC_ADDR_MASK                            (32'h7f)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_ADDR_STATIC_ADDR_VALID_LOW                       (15)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_ADDR_STATIC_ADDR_VALID_MASK                      (32'h8000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_ADDR_DYNAMIC_ADDR_LOW                            (16)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_ADDR_DYNAMIC_ADDR_MASK                           (32'h7f0000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_ADDR_DYNAMIC_ADDR_VALID_LOW                      (31)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_ADDR_DYNAMIC_ADDR_VALID_MASK                     (32'h80000000)
`endif
`ifndef I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CAPABILITIES
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CAPABILITIES                                            (32'h8c)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CAPABILITIES_SIMPLE_CRR_SUPPORT_LOW                     (5)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CAPABILITIES_SIMPLE_CRR_SUPPORT_MASK                    (32'h20)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CAPABILITIES_TARGET_XACT_SUPPORT_LOW                    (12)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CAPABILITIES_TARGET_XACT_SUPPORT_MASK                   (32'h1000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CAPABILITIES_DAA_SETAASA_SUPPORT_LOW                    (13)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CAPABILITIES_DAA_SETAASA_SUPPORT_MASK                   (32'h2000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CAPABILITIES_DAA_SETDASA_SUPPORT_LOW                    (14)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CAPABILITIES_DAA_SETDASA_SUPPORT_MASK                   (32'h4000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CAPABILITIES_DAA_ENTDAA_SUPPORT_LOW                     (15)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CAPABILITIES_DAA_ENTDAA_SUPPORT_MASK                    (32'h8000)
`endif
`ifndef I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRTUAL_DEVICE_CHAR
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRTUAL_DEVICE_CHAR                                     (32'h90)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRTUAL_DEVICE_CHAR_PID_HI_LOW                          (1)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRTUAL_DEVICE_CHAR_PID_HI_MASK                         (32'hfffe)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRTUAL_DEVICE_CHAR_DCR_LOW                             (16)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRTUAL_DEVICE_CHAR_DCR_MASK                            (32'hff0000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRTUAL_DEVICE_CHAR_BCR_VAR_LOW                         (24)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRTUAL_DEVICE_CHAR_BCR_VAR_MASK                        (32'h1f000000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRTUAL_DEVICE_CHAR_BCR_FIXED_LOW                       (29)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRTUAL_DEVICE_CHAR_BCR_FIXED_MASK                      (32'he0000000)
`endif
`ifndef I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_STATUS
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_STATUS                                                  (32'h94)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_STATUS_AC_CURRENT_OWN_LOW                               (2)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_STATUS_AC_CURRENT_OWN_MASK                              (32'h4)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_STATUS_SIMPLE_CRR_STATUS_LOW                            (5)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_STATUS_SIMPLE_CRR_STATUS_MASK                           (32'he0)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_STATUS_HJ_REQ_STATUS_LOW                                (8)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_STATUS_HJ_REQ_STATUS_MASK                               (32'h100)
`endif
`ifndef I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_CHAR
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_CHAR                                             (32'h98)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_CHAR_PID_HI_LOW                                  (1)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_CHAR_PID_HI_MASK                                 (32'hfffe)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_CHAR_DCR_LOW                                     (16)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_CHAR_DCR_MASK                                    (32'hff0000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_CHAR_BCR_VAR_LOW                                 (24)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_CHAR_BCR_VAR_MASK                                (32'h1f000000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_CHAR_BCR_FIXED_LOW                               (29)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_CHAR_BCR_FIXED_MASK                              (32'he0000000)
`endif
`ifndef I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_PID_LO
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_PID_LO                                           (32'h9c)
`endif
`ifndef I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS                                             (32'ha0)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_ACR_HANDOFF_OK_REMAIN_STAT_LOW              (0)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_ACR_HANDOFF_OK_REMAIN_STAT_MASK             (32'h1)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_ACR_HANDOFF_OK_PRIMED_STAT_LOW              (1)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_ACR_HANDOFF_OK_PRIMED_STAT_MASK             (32'h2)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_ACR_HANDOFF_ERR_FAIL_STAT_LOW               (2)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_ACR_HANDOFF_ERR_FAIL_STAT_MASK              (32'h4)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_ACR_HANDOFF_ERR_M3_STAT_LOW                 (3)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_ACR_HANDOFF_ERR_M3_STAT_MASK                (32'h8)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_CRR_RESPONSE_STAT_LOW                       (10)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_CRR_RESPONSE_STAT_MASK                      (32'h400)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_STBY_CR_DYN_ADDR_STAT_LOW                   (11)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_STBY_CR_DYN_ADDR_STAT_MASK                  (32'h800)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_STBY_CR_ACCEPT_NACKED_STAT_LOW              (12)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_STBY_CR_ACCEPT_NACKED_STAT_MASK             (32'h1000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_STBY_CR_ACCEPT_OK_STAT_LOW                  (13)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_STBY_CR_ACCEPT_OK_STAT_MASK                 (32'h2000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_STBY_CR_ACCEPT_ERR_STAT_LOW                 (14)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_STBY_CR_ACCEPT_ERR_STAT_MASK                (32'h4000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_STBY_CR_OP_RSTACT_STAT_LOW                  (16)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_STBY_CR_OP_RSTACT_STAT_MASK                 (32'h10000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_CCC_PARAM_MODIFIED_STAT_LOW                 (17)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_CCC_PARAM_MODIFIED_STAT_MASK                (32'h20000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_CCC_UNHANDLED_NACK_STAT_LOW                 (18)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_CCC_UNHANDLED_NACK_STAT_MASK                (32'h40000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_CCC_FATAL_RSTDAA_ERR_STAT_LOW               (19)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS_CCC_FATAL_RSTDAA_ERR_STAT_MASK              (32'h80000)
`endif
`ifndef I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRTUAL_DEVICE_PID_LO
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRTUAL_DEVICE_PID_LO                                   (32'ha4)
`endif
`ifndef I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE                                      (32'ha8)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_ACR_HANDOFF_OK_REMAIN_SIGNAL_EN_LOW  (0)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_ACR_HANDOFF_OK_REMAIN_SIGNAL_EN_MASK (32'h1)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_ACR_HANDOFF_OK_PRIMED_SIGNAL_EN_LOW  (1)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_ACR_HANDOFF_OK_PRIMED_SIGNAL_EN_MASK (32'h2)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_ACR_HANDOFF_ERR_FAIL_SIGNAL_EN_LOW   (2)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_ACR_HANDOFF_ERR_FAIL_SIGNAL_EN_MASK  (32'h4)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_ACR_HANDOFF_ERR_M3_SIGNAL_EN_LOW     (3)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_ACR_HANDOFF_ERR_M3_SIGNAL_EN_MASK    (32'h8)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_CRR_RESPONSE_SIGNAL_EN_LOW           (10)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_CRR_RESPONSE_SIGNAL_EN_MASK          (32'h400)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_STBY_CR_DYN_ADDR_SIGNAL_EN_LOW       (11)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_STBY_CR_DYN_ADDR_SIGNAL_EN_MASK      (32'h800)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_STBY_CR_ACCEPT_NACKED_SIGNAL_EN_LOW  (12)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_STBY_CR_ACCEPT_NACKED_SIGNAL_EN_MASK (32'h1000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_STBY_CR_ACCEPT_OK_SIGNAL_EN_LOW      (13)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_STBY_CR_ACCEPT_OK_SIGNAL_EN_MASK     (32'h2000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_STBY_CR_ACCEPT_ERR_SIGNAL_EN_LOW     (14)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_STBY_CR_ACCEPT_ERR_SIGNAL_EN_MASK    (32'h4000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_STBY_CR_OP_RSTACT_SIGNAL_EN_LOW      (16)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_STBY_CR_OP_RSTACT_SIGNAL_EN_MASK     (32'h10000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_CCC_PARAM_MODIFIED_SIGNAL_EN_LOW     (17)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_CCC_PARAM_MODIFIED_SIGNAL_EN_MASK    (32'h20000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_CCC_UNHANDLED_NACK_SIGNAL_EN_LOW     (18)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_CCC_UNHANDLED_NACK_SIGNAL_EN_MASK    (32'h40000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_CCC_FATAL_RSTDAA_ERR_SIGNAL_EN_LOW   (19)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_CCC_FATAL_RSTDAA_ERR_SIGNAL_EN_MASK  (32'h80000)
`endif
`ifndef I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE                                              (32'hac)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_CRR_RESPONSE_FORCE_LOW                       (10)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_CRR_RESPONSE_FORCE_MASK                      (32'h400)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_STBY_CR_DYN_ADDR_FORCE_LOW                   (11)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_STBY_CR_DYN_ADDR_FORCE_MASK                  (32'h800)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_STBY_CR_ACCEPT_NACKED_FORCE_LOW              (12)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_STBY_CR_ACCEPT_NACKED_FORCE_MASK             (32'h1000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_STBY_CR_ACCEPT_OK_FORCE_LOW                  (13)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_STBY_CR_ACCEPT_OK_FORCE_MASK                 (32'h2000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_STBY_CR_ACCEPT_ERR_FORCE_LOW                 (14)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_STBY_CR_ACCEPT_ERR_FORCE_MASK                (32'h4000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_STBY_CR_OP_RSTACT_FORCE_LOW                  (16)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_STBY_CR_OP_RSTACT_FORCE_MASK                 (32'h10000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_CCC_PARAM_MODIFIED_FORCE_LOW                 (17)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_CCC_PARAM_MODIFIED_FORCE_MASK                (32'h20000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_CCC_UNHANDLED_NACK_FORCE_LOW                 (18)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_CCC_UNHANDLED_NACK_FORCE_MASK                (32'h40000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_CCC_FATAL_RSTDAA_ERR_FORCE_LOW               (19)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_FORCE_CCC_FATAL_RSTDAA_ERR_FORCE_MASK              (32'h80000)
`endif
`ifndef I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CCC_CONFIG_GETCAPS
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CCC_CONFIG_GETCAPS                                      (32'hb0)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CCC_CONFIG_GETCAPS_F2_CRCAP1_BUS_CONFIG_LOW             (0)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CCC_CONFIG_GETCAPS_F2_CRCAP1_BUS_CONFIG_MASK            (32'h7)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CCC_CONFIG_GETCAPS_F2_CRCAP2_DEV_INTERACT_LOW           (8)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CCC_CONFIG_GETCAPS_F2_CRCAP2_DEV_INTERACT_MASK          (32'hf00)
`endif
`ifndef I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CCC_CONFIG_RSTACT_PARAMS
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CCC_CONFIG_RSTACT_PARAMS                                (32'hb4)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CCC_CONFIG_RSTACT_PARAMS_RST_ACTION_LOW                 (0)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CCC_CONFIG_RSTACT_PARAMS_RST_ACTION_MASK                (32'hff)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CCC_CONFIG_RSTACT_PARAMS_RESET_TIME_PERIPHERAL_LOW      (8)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CCC_CONFIG_RSTACT_PARAMS_RESET_TIME_PERIPHERAL_MASK     (32'hff00)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CCC_CONFIG_RSTACT_PARAMS_RESET_TIME_TARGET_LOW          (16)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CCC_CONFIG_RSTACT_PARAMS_RESET_TIME_TARGET_MASK         (32'hff0000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CCC_CONFIG_RSTACT_PARAMS_RESET_DYNAMIC_ADDR_LOW         (31)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CCC_CONFIG_RSTACT_PARAMS_RESET_DYNAMIC_ADDR_MASK        (32'h80000000)
`endif
`ifndef I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRT_DEVICE_ADDR
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRT_DEVICE_ADDR                                        (32'hb8)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRT_DEVICE_ADDR_VIRT_STATIC_ADDR_LOW                   (0)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRT_DEVICE_ADDR_VIRT_STATIC_ADDR_MASK                  (32'h7f)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRT_DEVICE_ADDR_VIRT_STATIC_ADDR_VALID_LOW             (15)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRT_DEVICE_ADDR_VIRT_STATIC_ADDR_VALID_MASK            (32'h8000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRT_DEVICE_ADDR_VIRT_DYNAMIC_ADDR_LOW                  (16)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRT_DEVICE_ADDR_VIRT_DYNAMIC_ADDR_MASK                 (32'h7f0000)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRT_DEVICE_ADDR_VIRT_DYNAMIC_ADDR_VALID_LOW            (31)
`define I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRT_DEVICE_ADDR_VIRT_DYNAMIC_ADDR_VALID_MASK           (32'h80000000)
`endif
`ifndef I3CCSR_I3C_EC_STDBYCTRLMODE___RSVD_3
`define I3CCSR_I3C_EC_STDBYCTRLMODE___RSVD_3                                                        (32'hbc)
`endif
`ifndef I3CCSR_I3C_EC_TTI_EXTCAP_HEADER
`define I3CCSR_I3C_EC_TTI_EXTCAP_HEADER                                                             (32'hc0)
`define I3CCSR_I3C_EC_TTI_EXTCAP_HEADER_CAP_ID_LOW                                                  (0)
`define I3CCSR_I3C_EC_TTI_EXTCAP_HEADER_CAP_ID_MASK                                                 (32'hff)
`define I3CCSR_I3C_EC_TTI_EXTCAP_HEADER_CAP_LENGTH_LOW                                              (8)
`define I3CCSR_I3C_EC_TTI_EXTCAP_HEADER_CAP_LENGTH_MASK                                             (32'hffff00)
`endif
`ifndef I3CCSR_I3C_EC_TTI_CONTROL
`define I3CCSR_I3C_EC_TTI_CONTROL                                                                   (32'hc4)
`define I3CCSR_I3C_EC_TTI_CONTROL_HJ_EN_LOW                                                         (10)
`define I3CCSR_I3C_EC_TTI_CONTROL_HJ_EN_MASK                                                        (32'h400)
`define I3CCSR_I3C_EC_TTI_CONTROL_CRR_EN_LOW                                                        (11)
`define I3CCSR_I3C_EC_TTI_CONTROL_CRR_EN_MASK                                                       (32'h800)
`define I3CCSR_I3C_EC_TTI_CONTROL_IBI_EN_LOW                                                        (12)
`define I3CCSR_I3C_EC_TTI_CONTROL_IBI_EN_MASK                                                       (32'h1000)
`define I3CCSR_I3C_EC_TTI_CONTROL_IBI_RETRY_NUM_LOW                                                 (13)
`define I3CCSR_I3C_EC_TTI_CONTROL_IBI_RETRY_NUM_MASK                                                (32'he000)
`endif
`ifndef I3CCSR_I3C_EC_TTI_STATUS
`define I3CCSR_I3C_EC_TTI_STATUS                                                                    (32'hc8)
`define I3CCSR_I3C_EC_TTI_STATUS_PROTOCOL_ERROR_LOW                                                 (13)
`define I3CCSR_I3C_EC_TTI_STATUS_PROTOCOL_ERROR_MASK                                                (32'h2000)
`define I3CCSR_I3C_EC_TTI_STATUS_LAST_IBI_STATUS_LOW                                                (14)
`define I3CCSR_I3C_EC_TTI_STATUS_LAST_IBI_STATUS_MASK                                               (32'hc000)
`endif
`ifndef I3CCSR_I3C_EC_TTI_RESET_CONTROL
`define I3CCSR_I3C_EC_TTI_RESET_CONTROL                                                             (32'hcc)
`define I3CCSR_I3C_EC_TTI_RESET_CONTROL_SOFT_RST_LOW                                                (0)
`define I3CCSR_I3C_EC_TTI_RESET_CONTROL_SOFT_RST_MASK                                               (32'h1)
`define I3CCSR_I3C_EC_TTI_RESET_CONTROL_TX_DESC_RST_LOW                                             (1)
`define I3CCSR_I3C_EC_TTI_RESET_CONTROL_TX_DESC_RST_MASK                                            (32'h2)
`define I3CCSR_I3C_EC_TTI_RESET_CONTROL_RX_DESC_RST_LOW                                             (2)
`define I3CCSR_I3C_EC_TTI_RESET_CONTROL_RX_DESC_RST_MASK                                            (32'h4)
`define I3CCSR_I3C_EC_TTI_RESET_CONTROL_TX_DATA_RST_LOW                                             (3)
`define I3CCSR_I3C_EC_TTI_RESET_CONTROL_TX_DATA_RST_MASK                                            (32'h8)
`define I3CCSR_I3C_EC_TTI_RESET_CONTROL_RX_DATA_RST_LOW                                             (4)
`define I3CCSR_I3C_EC_TTI_RESET_CONTROL_RX_DATA_RST_MASK                                            (32'h10)
`define I3CCSR_I3C_EC_TTI_RESET_CONTROL_IBI_QUEUE_RST_LOW                                           (5)
`define I3CCSR_I3C_EC_TTI_RESET_CONTROL_IBI_QUEUE_RST_MASK                                          (32'h20)
`endif
`ifndef I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS                                                          (32'hd0)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_RX_DESC_STAT_LOW                                         (0)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_RX_DESC_STAT_MASK                                        (32'h1)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_TX_DESC_STAT_LOW                                         (1)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_TX_DESC_STAT_MASK                                        (32'h2)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_RX_DESC_TIMEOUT_LOW                                      (2)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_RX_DESC_TIMEOUT_MASK                                     (32'h4)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_TX_DESC_TIMEOUT_LOW                                      (3)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_TX_DESC_TIMEOUT_MASK                                     (32'h8)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_TX_DATA_THLD_STAT_LOW                                    (8)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_TX_DATA_THLD_STAT_MASK                                   (32'h100)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_RX_DATA_THLD_STAT_LOW                                    (9)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_RX_DATA_THLD_STAT_MASK                                   (32'h200)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_TX_DESC_THLD_STAT_LOW                                    (10)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_TX_DESC_THLD_STAT_MASK                                   (32'h400)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_RX_DESC_THLD_STAT_LOW                                    (11)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_RX_DESC_THLD_STAT_MASK                                   (32'h800)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_IBI_THLD_STAT_LOW                                        (12)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_IBI_THLD_STAT_MASK                                       (32'h1000)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_IBI_DONE_LOW                                             (13)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_IBI_DONE_MASK                                            (32'h2000)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_PENDING_INTERRUPT_LOW                                    (15)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_PENDING_INTERRUPT_MASK                                   (32'h78000)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_TRANSFER_ABORT_STAT_LOW                                  (25)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_TRANSFER_ABORT_STAT_MASK                                 (32'h2000000)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_TX_DESC_COMPLETE_LOW                                     (26)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_TX_DESC_COMPLETE_MASK                                    (32'h4000000)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_TRANSFER_ERR_STAT_LOW                                    (31)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_TRANSFER_ERR_STAT_MASK                                   (32'h80000000)
`endif
`ifndef I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE                                                          (32'hd4)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_RX_DESC_STAT_EN_LOW                                      (0)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_RX_DESC_STAT_EN_MASK                                     (32'h1)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TX_DESC_STAT_EN_LOW                                      (1)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TX_DESC_STAT_EN_MASK                                     (32'h2)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_RX_DESC_TIMEOUT_EN_LOW                                   (2)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_RX_DESC_TIMEOUT_EN_MASK                                  (32'h4)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TX_DESC_TIMEOUT_EN_LOW                                   (3)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TX_DESC_TIMEOUT_EN_MASK                                  (32'h8)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TX_DATA_THLD_STAT_EN_LOW                                 (8)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TX_DATA_THLD_STAT_EN_MASK                                (32'h100)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_RX_DATA_THLD_STAT_EN_LOW                                 (9)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_RX_DATA_THLD_STAT_EN_MASK                                (32'h200)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TX_DESC_THLD_STAT_EN_LOW                                 (10)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TX_DESC_THLD_STAT_EN_MASK                                (32'h400)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_RX_DESC_THLD_STAT_EN_LOW                                 (11)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_RX_DESC_THLD_STAT_EN_MASK                                (32'h800)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_IBI_THLD_STAT_EN_LOW                                     (12)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_IBI_THLD_STAT_EN_MASK                                    (32'h1000)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_IBI_DONE_EN_LOW                                          (13)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_IBI_DONE_EN_MASK                                         (32'h2000)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TRANSFER_ABORT_STAT_EN_LOW                               (25)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TRANSFER_ABORT_STAT_EN_MASK                              (32'h2000000)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TX_DESC_COMPLETE_EN_LOW                                  (26)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TX_DESC_COMPLETE_EN_MASK                                 (32'h4000000)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TRANSFER_ERR_STAT_EN_LOW                                 (31)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TRANSFER_ERR_STAT_EN_MASK                                (32'h80000000)
`endif
`ifndef I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE                                                           (32'hd8)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_RX_DESC_STAT_FORCE_LOW                                    (0)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_RX_DESC_STAT_FORCE_MASK                                   (32'h1)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_TX_DESC_STAT_FORCE_LOW                                    (1)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_TX_DESC_STAT_FORCE_MASK                                   (32'h2)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_RX_DESC_TIMEOUT_FORCE_LOW                                 (2)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_RX_DESC_TIMEOUT_FORCE_MASK                                (32'h4)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_TX_DESC_TIMEOUT_FORCE_LOW                                 (3)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_TX_DESC_TIMEOUT_FORCE_MASK                                (32'h8)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_TX_DATA_THLD_FORCE_LOW                                    (8)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_TX_DATA_THLD_FORCE_MASK                                   (32'h100)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_RX_DATA_THLD_FORCE_LOW                                    (9)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_RX_DATA_THLD_FORCE_MASK                                   (32'h200)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_TX_DESC_THLD_FORCE_LOW                                    (10)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_TX_DESC_THLD_FORCE_MASK                                   (32'h400)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_RX_DESC_THLD_FORCE_LOW                                    (11)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_RX_DESC_THLD_FORCE_MASK                                   (32'h800)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_IBI_THLD_FORCE_LOW                                        (12)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_IBI_THLD_FORCE_MASK                                       (32'h1000)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_IBI_DONE_FORCE_LOW                                        (13)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_IBI_DONE_FORCE_MASK                                       (32'h2000)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_TRANSFER_ABORT_STAT_FORCE_LOW                             (25)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_TRANSFER_ABORT_STAT_FORCE_MASK                            (32'h2000000)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_TX_DESC_COMPLETE_FORCE_LOW                                (26)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_TX_DESC_COMPLETE_FORCE_MASK                               (32'h4000000)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_TRANSFER_ERR_STAT_FORCE_LOW                               (31)
`define I3CCSR_I3C_EC_TTI_INTERRUPT_FORCE_TRANSFER_ERR_STAT_FORCE_MASK                              (32'h80000000)
`endif
`ifndef I3CCSR_I3C_EC_TTI_RX_DESC_QUEUE_PORT
`define I3CCSR_I3C_EC_TTI_RX_DESC_QUEUE_PORT                                                        (32'hdc)
`endif
`ifndef I3CCSR_I3C_EC_TTI_RX_DATA_PORT
`define I3CCSR_I3C_EC_TTI_RX_DATA_PORT                                                              (32'he0)
`endif
`ifndef I3CCSR_I3C_EC_TTI_TX_DESC_QUEUE_PORT
`define I3CCSR_I3C_EC_TTI_TX_DESC_QUEUE_PORT                                                        (32'he4)
`endif
`ifndef I3CCSR_I3C_EC_TTI_TX_DATA_PORT
`define I3CCSR_I3C_EC_TTI_TX_DATA_PORT                                                              (32'he8)
`endif
`ifndef I3CCSR_I3C_EC_TTI_IBI_PORT
`define I3CCSR_I3C_EC_TTI_IBI_PORT                                                                  (32'hec)
`endif
`ifndef I3CCSR_I3C_EC_TTI_QUEUE_SIZE
`define I3CCSR_I3C_EC_TTI_QUEUE_SIZE                                                                (32'hf0)
`define I3CCSR_I3C_EC_TTI_QUEUE_SIZE_RX_DESC_BUFFER_SIZE_LOW                                        (0)
`define I3CCSR_I3C_EC_TTI_QUEUE_SIZE_RX_DESC_BUFFER_SIZE_MASK                                       (32'hff)
`define I3CCSR_I3C_EC_TTI_QUEUE_SIZE_TX_DESC_BUFFER_SIZE_LOW                                        (8)
`define I3CCSR_I3C_EC_TTI_QUEUE_SIZE_TX_DESC_BUFFER_SIZE_MASK                                       (32'hff00)
`define I3CCSR_I3C_EC_TTI_QUEUE_SIZE_RX_DATA_BUFFER_SIZE_LOW                                        (16)
`define I3CCSR_I3C_EC_TTI_QUEUE_SIZE_RX_DATA_BUFFER_SIZE_MASK                                       (32'hff0000)
`define I3CCSR_I3C_EC_TTI_QUEUE_SIZE_TX_DATA_BUFFER_SIZE_LOW                                        (24)
`define I3CCSR_I3C_EC_TTI_QUEUE_SIZE_TX_DATA_BUFFER_SIZE_MASK                                       (32'hff000000)
`endif
`ifndef I3CCSR_I3C_EC_TTI_IBI_QUEUE_SIZE
`define I3CCSR_I3C_EC_TTI_IBI_QUEUE_SIZE                                                            (32'hf4)
`define I3CCSR_I3C_EC_TTI_IBI_QUEUE_SIZE_IBI_QUEUE_SIZE_LOW                                         (0)
`define I3CCSR_I3C_EC_TTI_IBI_QUEUE_SIZE_IBI_QUEUE_SIZE_MASK                                        (32'hff)
`endif
`ifndef I3CCSR_I3C_EC_TTI_QUEUE_THLD_CTRL
`define I3CCSR_I3C_EC_TTI_QUEUE_THLD_CTRL                                                           (32'hf8)
`define I3CCSR_I3C_EC_TTI_QUEUE_THLD_CTRL_TX_DESC_THLD_LOW                                          (0)
`define I3CCSR_I3C_EC_TTI_QUEUE_THLD_CTRL_TX_DESC_THLD_MASK                                         (32'hff)
`define I3CCSR_I3C_EC_TTI_QUEUE_THLD_CTRL_RX_DESC_THLD_LOW                                          (8)
`define I3CCSR_I3C_EC_TTI_QUEUE_THLD_CTRL_RX_DESC_THLD_MASK                                         (32'hff00)
`define I3CCSR_I3C_EC_TTI_QUEUE_THLD_CTRL_IBI_THLD_LOW                                              (24)
`define I3CCSR_I3C_EC_TTI_QUEUE_THLD_CTRL_IBI_THLD_MASK                                             (32'hff000000)
`endif
`ifndef I3CCSR_I3C_EC_TTI_DATA_BUFFER_THLD_CTRL
`define I3CCSR_I3C_EC_TTI_DATA_BUFFER_THLD_CTRL                                                     (32'hfc)
`define I3CCSR_I3C_EC_TTI_DATA_BUFFER_THLD_CTRL_TX_DATA_THLD_LOW                                    (0)
`define I3CCSR_I3C_EC_TTI_DATA_BUFFER_THLD_CTRL_TX_DATA_THLD_MASK                                   (32'h7)
`define I3CCSR_I3C_EC_TTI_DATA_BUFFER_THLD_CTRL_RX_DATA_THLD_LOW                                    (8)
`define I3CCSR_I3C_EC_TTI_DATA_BUFFER_THLD_CTRL_RX_DATA_THLD_MASK                                   (32'h700)
`define I3CCSR_I3C_EC_TTI_DATA_BUFFER_THLD_CTRL_TX_START_THLD_LOW                                   (16)
`define I3CCSR_I3C_EC_TTI_DATA_BUFFER_THLD_CTRL_TX_START_THLD_MASK                                  (32'h70000)
`define I3CCSR_I3C_EC_TTI_DATA_BUFFER_THLD_CTRL_RX_START_THLD_LOW                                   (24)
`define I3CCSR_I3C_EC_TTI_DATA_BUFFER_THLD_CTRL_RX_START_THLD_MASK                                  (32'h7000000)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_EXTCAP_HEADER
`define I3CCSR_I3C_EC_SOCMGMTIF_EXTCAP_HEADER                                                       (32'h100)
`define I3CCSR_I3C_EC_SOCMGMTIF_EXTCAP_HEADER_CAP_ID_LOW                                            (0)
`define I3CCSR_I3C_EC_SOCMGMTIF_EXTCAP_HEADER_CAP_ID_MASK                                           (32'hff)
`define I3CCSR_I3C_EC_SOCMGMTIF_EXTCAP_HEADER_CAP_LENGTH_LOW                                        (8)
`define I3CCSR_I3C_EC_SOCMGMTIF_EXTCAP_HEADER_CAP_LENGTH_MASK                                       (32'hffff00)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_SOC_MGMT_CONTROL
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_MGMT_CONTROL                                                    (32'h104)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_SOC_MGMT_STATUS
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_MGMT_STATUS                                                     (32'h108)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_CFG
`define I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_CFG                                                        (32'h10c)
`define I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_CFG_REC_INTF_BYPASS_LOW                                    (0)
`define I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_CFG_REC_INTF_BYPASS_MASK                                   (32'h1)
`define I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_CFG_REC_PAYLOAD_DONE_LOW                                   (1)
`define I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_CFG_REC_PAYLOAD_DONE_MASK                                  (32'h2)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_REG_W1C_ACCESS
`define I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_REG_W1C_ACCESS                                             (32'h110)
`define I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_REG_W1C_ACCESS_DEVICE_RESET_CTRL_LOW                       (0)
`define I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_REG_W1C_ACCESS_DEVICE_RESET_CTRL_MASK                      (32'hff)
`define I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_REG_W1C_ACCESS_RECOVERY_CTRL_ACTIVATE_REC_IMG_LOW          (8)
`define I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_REG_W1C_ACCESS_RECOVERY_CTRL_ACTIVATE_REC_IMG_MASK         (32'hff00)
`define I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_REG_W1C_ACCESS_INDIRECT_FIFO_CTRL_RESET_LOW                (16)
`define I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_REG_W1C_ACCESS_INDIRECT_FIFO_CTRL_RESET_MASK               (32'hff0000)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_SOC_MGMT_RSVD_2
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_MGMT_RSVD_2                                                     (32'h114)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_SOC_MGMT_RSVD_3
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_MGMT_RSVD_3                                                     (32'h118)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF                                                        (32'h11c)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_INPUT_ENABLE_LOW                                       (0)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_INPUT_ENABLE_MASK                                      (32'h1)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_SCHMITT_EN_LOW                                         (1)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_SCHMITT_EN_MASK                                        (32'h2)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_KEEPER_EN_LOW                                          (2)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_KEEPER_EN_MASK                                         (32'h4)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_PULL_DIR_LOW                                           (3)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_PULL_DIR_MASK                                          (32'h8)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_PULL_EN_LOW                                            (4)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_PULL_EN_MASK                                           (32'h10)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_IO_INVERSION_LOW                                       (5)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_IO_INVERSION_MASK                                      (32'h20)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_OD_EN_LOW                                              (6)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_OD_EN_MASK                                             (32'h40)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_VIRTUAL_OD_EN_LOW                                      (7)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_VIRTUAL_OD_EN_MASK                                     (32'h80)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_PAD_TYPE_LOW                                           (24)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_CONF_PAD_TYPE_MASK                                          (32'hff000000)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_ATTR
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_ATTR                                                        (32'h120)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_ATTR_DRIVE_SLEW_RATE_LOW                                    (8)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_ATTR_DRIVE_SLEW_RATE_MASK                                   (32'hff00)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_ATTR_DRIVE_STRENGTH_LOW                                     (24)
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_PAD_ATTR_DRIVE_STRENGTH_MASK                                    (32'hff000000)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_SOC_MGMT_FEATURE_2
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_MGMT_FEATURE_2                                                  (32'h124)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_SOC_MGMT_FEATURE_3
`define I3CCSR_I3C_EC_SOCMGMTIF_SOC_MGMT_FEATURE_3                                                  (32'h128)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_T_R_REG
`define I3CCSR_I3C_EC_SOCMGMTIF_T_R_REG                                                             (32'h12c)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_R_REG_T_R_LOW                                                     (0)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_R_REG_T_R_MASK                                                    (32'hfffff)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_T_F_REG
`define I3CCSR_I3C_EC_SOCMGMTIF_T_F_REG                                                             (32'h130)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_F_REG_T_F_LOW                                                     (0)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_F_REG_T_F_MASK                                                    (32'hfffff)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_T_SU_DAT_REG
`define I3CCSR_I3C_EC_SOCMGMTIF_T_SU_DAT_REG                                                        (32'h134)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_SU_DAT_REG_T_SU_DAT_LOW                                           (0)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_SU_DAT_REG_T_SU_DAT_MASK                                          (32'hfffff)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_T_HD_DAT_REG
`define I3CCSR_I3C_EC_SOCMGMTIF_T_HD_DAT_REG                                                        (32'h138)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_HD_DAT_REG_T_HD_DAT_LOW                                           (0)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_HD_DAT_REG_T_HD_DAT_MASK                                          (32'hfffff)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_T_HIGH_REG
`define I3CCSR_I3C_EC_SOCMGMTIF_T_HIGH_REG                                                          (32'h13c)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_HIGH_REG_T_HIGH_LOW                                               (0)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_HIGH_REG_T_HIGH_MASK                                              (32'hfffff)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_T_LOW_REG
`define I3CCSR_I3C_EC_SOCMGMTIF_T_LOW_REG                                                           (32'h140)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_LOW_REG_T_LOW_LOW                                                 (0)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_LOW_REG_T_LOW_MASK                                                (32'hfffff)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_T_HD_STA_REG
`define I3CCSR_I3C_EC_SOCMGMTIF_T_HD_STA_REG                                                        (32'h144)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_HD_STA_REG_T_HD_STA_LOW                                           (0)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_HD_STA_REG_T_HD_STA_MASK                                          (32'hfffff)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_T_SU_STA_REG
`define I3CCSR_I3C_EC_SOCMGMTIF_T_SU_STA_REG                                                        (32'h148)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_SU_STA_REG_T_SU_STA_LOW                                           (0)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_SU_STA_REG_T_SU_STA_MASK                                          (32'hfffff)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_T_SU_STO_REG
`define I3CCSR_I3C_EC_SOCMGMTIF_T_SU_STO_REG                                                        (32'h14c)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_SU_STO_REG_T_SU_STO_LOW                                           (0)
`define I3CCSR_I3C_EC_SOCMGMTIF_T_SU_STO_REG_T_SU_STO_MASK                                          (32'hfffff)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_T_FREE_REG
`define I3CCSR_I3C_EC_SOCMGMTIF_T_FREE_REG                                                          (32'h150)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_T_AVAL_REG
`define I3CCSR_I3C_EC_SOCMGMTIF_T_AVAL_REG                                                          (32'h154)
`endif
`ifndef I3CCSR_I3C_EC_SOCMGMTIF_T_IDLE_REG
`define I3CCSR_I3C_EC_SOCMGMTIF_T_IDLE_REG                                                          (32'h158)
`endif
`ifndef I3CCSR_I3C_EC_CTRLCFG_EXTCAP_HEADER
`define I3CCSR_I3C_EC_CTRLCFG_EXTCAP_HEADER                                                         (32'h160)
`define I3CCSR_I3C_EC_CTRLCFG_EXTCAP_HEADER_CAP_ID_LOW                                              (0)
`define I3CCSR_I3C_EC_CTRLCFG_EXTCAP_HEADER_CAP_ID_MASK                                             (32'hff)
`define I3CCSR_I3C_EC_CTRLCFG_EXTCAP_HEADER_CAP_LENGTH_LOW                                          (8)
`define I3CCSR_I3C_EC_CTRLCFG_EXTCAP_HEADER_CAP_LENGTH_MASK                                         (32'hffff00)
`endif
`ifndef I3CCSR_I3C_EC_CTRLCFG_CONTROLLER_CONFIG
`define I3CCSR_I3C_EC_CTRLCFG_CONTROLLER_CONFIG                                                     (32'h164)
`define I3CCSR_I3C_EC_CTRLCFG_CONTROLLER_CONFIG_OPERATION_MODE_LOW                                  (4)
`define I3CCSR_I3C_EC_CTRLCFG_CONTROLLER_CONFIG_OPERATION_MODE_MASK                                 (32'h30)
`endif
`ifndef I3CCSR_I3C_EC_TERMINATION_EXTCAP_HEADER
`define I3CCSR_I3C_EC_TERMINATION_EXTCAP_HEADER                                                     (32'h168)
`define I3CCSR_I3C_EC_TERMINATION_EXTCAP_HEADER_CAP_ID_LOW                                          (0)
`define I3CCSR_I3C_EC_TERMINATION_EXTCAP_HEADER_CAP_ID_MASK                                         (32'hff)
`define I3CCSR_I3C_EC_TERMINATION_EXTCAP_HEADER_CAP_LENGTH_LOW                                      (8)
`define I3CCSR_I3C_EC_TERMINATION_EXTCAP_HEADER_CAP_LENGTH_MASK                                     (32'hffff00)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_0
`define I3CCSR_DAT_DAT_MEMORY_0                                                                     (32'h0)
`define I3CCSR_DAT_DAT_MEMORY_0_STATIC_ADDRESS_LOW                                                  (0)
`define I3CCSR_DAT_DAT_MEMORY_0_STATIC_ADDRESS_MASK                                                 (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_0_IBI_PAYLOAD_LOW                                                     (12)
`define I3CCSR_DAT_DAT_MEMORY_0_IBI_PAYLOAD_MASK                                                    (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_0_IBI_REJECT_LOW                                                      (13)
`define I3CCSR_DAT_DAT_MEMORY_0_IBI_REJECT_MASK                                                     (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_0_CRR_REJECT_LOW                                                      (14)
`define I3CCSR_DAT_DAT_MEMORY_0_CRR_REJECT_MASK                                                     (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_0_TS_LOW                                                              (15)
`define I3CCSR_DAT_DAT_MEMORY_0_TS_MASK                                                             (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_0_DYNAMIC_ADDRESS_LOW                                                 (16)
`define I3CCSR_DAT_DAT_MEMORY_0_DYNAMIC_ADDRESS_MASK                                                (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_0_RING_ID_LOW                                                         (26)
`define I3CCSR_DAT_DAT_MEMORY_0_RING_ID_MASK                                                        (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_0_DEV_NACK_RETRY_CNT_LOW                                              (29)
`define I3CCSR_DAT_DAT_MEMORY_0_DEV_NACK_RETRY_CNT_MASK                                             (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_0_DEVICE_LOW                                                          (31)
`define I3CCSR_DAT_DAT_MEMORY_0_DEVICE_MASK                                                         (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_0_AUTOCMD_MASK_LOW                                                    (32)
`define I3CCSR_DAT_DAT_MEMORY_0_AUTOCMD_MASK_MASK                                                   (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_0_AUTOCMD_VALUE_LOW                                                   (40)
`define I3CCSR_DAT_DAT_MEMORY_0_AUTOCMD_VALUE_MASK                                                  (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_0_AUTOCMD_MODE_LOW                                                    (48)
`define I3CCSR_DAT_DAT_MEMORY_0_AUTOCMD_MODE_MASK                                                   (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_0_AUTOCMD_HDR_CODE_LOW                                                (51)
`define I3CCSR_DAT_DAT_MEMORY_0_AUTOCMD_HDR_CODE_MASK                                               (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_1
`define I3CCSR_DAT_DAT_MEMORY_1                                                                     (32'h8)
`define I3CCSR_DAT_DAT_MEMORY_1_STATIC_ADDRESS_LOW                                                  (0)
`define I3CCSR_DAT_DAT_MEMORY_1_STATIC_ADDRESS_MASK                                                 (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_1_IBI_PAYLOAD_LOW                                                     (12)
`define I3CCSR_DAT_DAT_MEMORY_1_IBI_PAYLOAD_MASK                                                    (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_1_IBI_REJECT_LOW                                                      (13)
`define I3CCSR_DAT_DAT_MEMORY_1_IBI_REJECT_MASK                                                     (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_1_CRR_REJECT_LOW                                                      (14)
`define I3CCSR_DAT_DAT_MEMORY_1_CRR_REJECT_MASK                                                     (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_1_TS_LOW                                                              (15)
`define I3CCSR_DAT_DAT_MEMORY_1_TS_MASK                                                             (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_1_DYNAMIC_ADDRESS_LOW                                                 (16)
`define I3CCSR_DAT_DAT_MEMORY_1_DYNAMIC_ADDRESS_MASK                                                (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_1_RING_ID_LOW                                                         (26)
`define I3CCSR_DAT_DAT_MEMORY_1_RING_ID_MASK                                                        (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_1_DEV_NACK_RETRY_CNT_LOW                                              (29)
`define I3CCSR_DAT_DAT_MEMORY_1_DEV_NACK_RETRY_CNT_MASK                                             (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_1_DEVICE_LOW                                                          (31)
`define I3CCSR_DAT_DAT_MEMORY_1_DEVICE_MASK                                                         (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_1_AUTOCMD_MASK_LOW                                                    (32)
`define I3CCSR_DAT_DAT_MEMORY_1_AUTOCMD_MASK_MASK                                                   (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_1_AUTOCMD_VALUE_LOW                                                   (40)
`define I3CCSR_DAT_DAT_MEMORY_1_AUTOCMD_VALUE_MASK                                                  (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_1_AUTOCMD_MODE_LOW                                                    (48)
`define I3CCSR_DAT_DAT_MEMORY_1_AUTOCMD_MODE_MASK                                                   (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_1_AUTOCMD_HDR_CODE_LOW                                                (51)
`define I3CCSR_DAT_DAT_MEMORY_1_AUTOCMD_HDR_CODE_MASK                                               (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_2
`define I3CCSR_DAT_DAT_MEMORY_2                                                                     (32'h10)
`define I3CCSR_DAT_DAT_MEMORY_2_STATIC_ADDRESS_LOW                                                  (0)
`define I3CCSR_DAT_DAT_MEMORY_2_STATIC_ADDRESS_MASK                                                 (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_2_IBI_PAYLOAD_LOW                                                     (12)
`define I3CCSR_DAT_DAT_MEMORY_2_IBI_PAYLOAD_MASK                                                    (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_2_IBI_REJECT_LOW                                                      (13)
`define I3CCSR_DAT_DAT_MEMORY_2_IBI_REJECT_MASK                                                     (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_2_CRR_REJECT_LOW                                                      (14)
`define I3CCSR_DAT_DAT_MEMORY_2_CRR_REJECT_MASK                                                     (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_2_TS_LOW                                                              (15)
`define I3CCSR_DAT_DAT_MEMORY_2_TS_MASK                                                             (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_2_DYNAMIC_ADDRESS_LOW                                                 (16)
`define I3CCSR_DAT_DAT_MEMORY_2_DYNAMIC_ADDRESS_MASK                                                (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_2_RING_ID_LOW                                                         (26)
`define I3CCSR_DAT_DAT_MEMORY_2_RING_ID_MASK                                                        (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_2_DEV_NACK_RETRY_CNT_LOW                                              (29)
`define I3CCSR_DAT_DAT_MEMORY_2_DEV_NACK_RETRY_CNT_MASK                                             (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_2_DEVICE_LOW                                                          (31)
`define I3CCSR_DAT_DAT_MEMORY_2_DEVICE_MASK                                                         (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_2_AUTOCMD_MASK_LOW                                                    (32)
`define I3CCSR_DAT_DAT_MEMORY_2_AUTOCMD_MASK_MASK                                                   (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_2_AUTOCMD_VALUE_LOW                                                   (40)
`define I3CCSR_DAT_DAT_MEMORY_2_AUTOCMD_VALUE_MASK                                                  (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_2_AUTOCMD_MODE_LOW                                                    (48)
`define I3CCSR_DAT_DAT_MEMORY_2_AUTOCMD_MODE_MASK                                                   (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_2_AUTOCMD_HDR_CODE_LOW                                                (51)
`define I3CCSR_DAT_DAT_MEMORY_2_AUTOCMD_HDR_CODE_MASK                                               (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_3
`define I3CCSR_DAT_DAT_MEMORY_3                                                                     (32'h18)
`define I3CCSR_DAT_DAT_MEMORY_3_STATIC_ADDRESS_LOW                                                  (0)
`define I3CCSR_DAT_DAT_MEMORY_3_STATIC_ADDRESS_MASK                                                 (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_3_IBI_PAYLOAD_LOW                                                     (12)
`define I3CCSR_DAT_DAT_MEMORY_3_IBI_PAYLOAD_MASK                                                    (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_3_IBI_REJECT_LOW                                                      (13)
`define I3CCSR_DAT_DAT_MEMORY_3_IBI_REJECT_MASK                                                     (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_3_CRR_REJECT_LOW                                                      (14)
`define I3CCSR_DAT_DAT_MEMORY_3_CRR_REJECT_MASK                                                     (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_3_TS_LOW                                                              (15)
`define I3CCSR_DAT_DAT_MEMORY_3_TS_MASK                                                             (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_3_DYNAMIC_ADDRESS_LOW                                                 (16)
`define I3CCSR_DAT_DAT_MEMORY_3_DYNAMIC_ADDRESS_MASK                                                (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_3_RING_ID_LOW                                                         (26)
`define I3CCSR_DAT_DAT_MEMORY_3_RING_ID_MASK                                                        (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_3_DEV_NACK_RETRY_CNT_LOW                                              (29)
`define I3CCSR_DAT_DAT_MEMORY_3_DEV_NACK_RETRY_CNT_MASK                                             (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_3_DEVICE_LOW                                                          (31)
`define I3CCSR_DAT_DAT_MEMORY_3_DEVICE_MASK                                                         (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_3_AUTOCMD_MASK_LOW                                                    (32)
`define I3CCSR_DAT_DAT_MEMORY_3_AUTOCMD_MASK_MASK                                                   (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_3_AUTOCMD_VALUE_LOW                                                   (40)
`define I3CCSR_DAT_DAT_MEMORY_3_AUTOCMD_VALUE_MASK                                                  (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_3_AUTOCMD_MODE_LOW                                                    (48)
`define I3CCSR_DAT_DAT_MEMORY_3_AUTOCMD_MODE_MASK                                                   (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_3_AUTOCMD_HDR_CODE_LOW                                                (51)
`define I3CCSR_DAT_DAT_MEMORY_3_AUTOCMD_HDR_CODE_MASK                                               (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_4
`define I3CCSR_DAT_DAT_MEMORY_4                                                                     (32'h20)
`define I3CCSR_DAT_DAT_MEMORY_4_STATIC_ADDRESS_LOW                                                  (0)
`define I3CCSR_DAT_DAT_MEMORY_4_STATIC_ADDRESS_MASK                                                 (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_4_IBI_PAYLOAD_LOW                                                     (12)
`define I3CCSR_DAT_DAT_MEMORY_4_IBI_PAYLOAD_MASK                                                    (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_4_IBI_REJECT_LOW                                                      (13)
`define I3CCSR_DAT_DAT_MEMORY_4_IBI_REJECT_MASK                                                     (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_4_CRR_REJECT_LOW                                                      (14)
`define I3CCSR_DAT_DAT_MEMORY_4_CRR_REJECT_MASK                                                     (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_4_TS_LOW                                                              (15)
`define I3CCSR_DAT_DAT_MEMORY_4_TS_MASK                                                             (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_4_DYNAMIC_ADDRESS_LOW                                                 (16)
`define I3CCSR_DAT_DAT_MEMORY_4_DYNAMIC_ADDRESS_MASK                                                (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_4_RING_ID_LOW                                                         (26)
`define I3CCSR_DAT_DAT_MEMORY_4_RING_ID_MASK                                                        (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_4_DEV_NACK_RETRY_CNT_LOW                                              (29)
`define I3CCSR_DAT_DAT_MEMORY_4_DEV_NACK_RETRY_CNT_MASK                                             (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_4_DEVICE_LOW                                                          (31)
`define I3CCSR_DAT_DAT_MEMORY_4_DEVICE_MASK                                                         (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_4_AUTOCMD_MASK_LOW                                                    (32)
`define I3CCSR_DAT_DAT_MEMORY_4_AUTOCMD_MASK_MASK                                                   (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_4_AUTOCMD_VALUE_LOW                                                   (40)
`define I3CCSR_DAT_DAT_MEMORY_4_AUTOCMD_VALUE_MASK                                                  (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_4_AUTOCMD_MODE_LOW                                                    (48)
`define I3CCSR_DAT_DAT_MEMORY_4_AUTOCMD_MODE_MASK                                                   (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_4_AUTOCMD_HDR_CODE_LOW                                                (51)
`define I3CCSR_DAT_DAT_MEMORY_4_AUTOCMD_HDR_CODE_MASK                                               (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_5
`define I3CCSR_DAT_DAT_MEMORY_5                                                                     (32'h28)
`define I3CCSR_DAT_DAT_MEMORY_5_STATIC_ADDRESS_LOW                                                  (0)
`define I3CCSR_DAT_DAT_MEMORY_5_STATIC_ADDRESS_MASK                                                 (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_5_IBI_PAYLOAD_LOW                                                     (12)
`define I3CCSR_DAT_DAT_MEMORY_5_IBI_PAYLOAD_MASK                                                    (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_5_IBI_REJECT_LOW                                                      (13)
`define I3CCSR_DAT_DAT_MEMORY_5_IBI_REJECT_MASK                                                     (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_5_CRR_REJECT_LOW                                                      (14)
`define I3CCSR_DAT_DAT_MEMORY_5_CRR_REJECT_MASK                                                     (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_5_TS_LOW                                                              (15)
`define I3CCSR_DAT_DAT_MEMORY_5_TS_MASK                                                             (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_5_DYNAMIC_ADDRESS_LOW                                                 (16)
`define I3CCSR_DAT_DAT_MEMORY_5_DYNAMIC_ADDRESS_MASK                                                (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_5_RING_ID_LOW                                                         (26)
`define I3CCSR_DAT_DAT_MEMORY_5_RING_ID_MASK                                                        (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_5_DEV_NACK_RETRY_CNT_LOW                                              (29)
`define I3CCSR_DAT_DAT_MEMORY_5_DEV_NACK_RETRY_CNT_MASK                                             (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_5_DEVICE_LOW                                                          (31)
`define I3CCSR_DAT_DAT_MEMORY_5_DEVICE_MASK                                                         (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_5_AUTOCMD_MASK_LOW                                                    (32)
`define I3CCSR_DAT_DAT_MEMORY_5_AUTOCMD_MASK_MASK                                                   (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_5_AUTOCMD_VALUE_LOW                                                   (40)
`define I3CCSR_DAT_DAT_MEMORY_5_AUTOCMD_VALUE_MASK                                                  (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_5_AUTOCMD_MODE_LOW                                                    (48)
`define I3CCSR_DAT_DAT_MEMORY_5_AUTOCMD_MODE_MASK                                                   (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_5_AUTOCMD_HDR_CODE_LOW                                                (51)
`define I3CCSR_DAT_DAT_MEMORY_5_AUTOCMD_HDR_CODE_MASK                                               (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_6
`define I3CCSR_DAT_DAT_MEMORY_6                                                                     (32'h30)
`define I3CCSR_DAT_DAT_MEMORY_6_STATIC_ADDRESS_LOW                                                  (0)
`define I3CCSR_DAT_DAT_MEMORY_6_STATIC_ADDRESS_MASK                                                 (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_6_IBI_PAYLOAD_LOW                                                     (12)
`define I3CCSR_DAT_DAT_MEMORY_6_IBI_PAYLOAD_MASK                                                    (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_6_IBI_REJECT_LOW                                                      (13)
`define I3CCSR_DAT_DAT_MEMORY_6_IBI_REJECT_MASK                                                     (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_6_CRR_REJECT_LOW                                                      (14)
`define I3CCSR_DAT_DAT_MEMORY_6_CRR_REJECT_MASK                                                     (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_6_TS_LOW                                                              (15)
`define I3CCSR_DAT_DAT_MEMORY_6_TS_MASK                                                             (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_6_DYNAMIC_ADDRESS_LOW                                                 (16)
`define I3CCSR_DAT_DAT_MEMORY_6_DYNAMIC_ADDRESS_MASK                                                (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_6_RING_ID_LOW                                                         (26)
`define I3CCSR_DAT_DAT_MEMORY_6_RING_ID_MASK                                                        (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_6_DEV_NACK_RETRY_CNT_LOW                                              (29)
`define I3CCSR_DAT_DAT_MEMORY_6_DEV_NACK_RETRY_CNT_MASK                                             (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_6_DEVICE_LOW                                                          (31)
`define I3CCSR_DAT_DAT_MEMORY_6_DEVICE_MASK                                                         (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_6_AUTOCMD_MASK_LOW                                                    (32)
`define I3CCSR_DAT_DAT_MEMORY_6_AUTOCMD_MASK_MASK                                                   (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_6_AUTOCMD_VALUE_LOW                                                   (40)
`define I3CCSR_DAT_DAT_MEMORY_6_AUTOCMD_VALUE_MASK                                                  (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_6_AUTOCMD_MODE_LOW                                                    (48)
`define I3CCSR_DAT_DAT_MEMORY_6_AUTOCMD_MODE_MASK                                                   (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_6_AUTOCMD_HDR_CODE_LOW                                                (51)
`define I3CCSR_DAT_DAT_MEMORY_6_AUTOCMD_HDR_CODE_MASK                                               (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_7
`define I3CCSR_DAT_DAT_MEMORY_7                                                                     (32'h38)
`define I3CCSR_DAT_DAT_MEMORY_7_STATIC_ADDRESS_LOW                                                  (0)
`define I3CCSR_DAT_DAT_MEMORY_7_STATIC_ADDRESS_MASK                                                 (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_7_IBI_PAYLOAD_LOW                                                     (12)
`define I3CCSR_DAT_DAT_MEMORY_7_IBI_PAYLOAD_MASK                                                    (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_7_IBI_REJECT_LOW                                                      (13)
`define I3CCSR_DAT_DAT_MEMORY_7_IBI_REJECT_MASK                                                     (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_7_CRR_REJECT_LOW                                                      (14)
`define I3CCSR_DAT_DAT_MEMORY_7_CRR_REJECT_MASK                                                     (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_7_TS_LOW                                                              (15)
`define I3CCSR_DAT_DAT_MEMORY_7_TS_MASK                                                             (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_7_DYNAMIC_ADDRESS_LOW                                                 (16)
`define I3CCSR_DAT_DAT_MEMORY_7_DYNAMIC_ADDRESS_MASK                                                (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_7_RING_ID_LOW                                                         (26)
`define I3CCSR_DAT_DAT_MEMORY_7_RING_ID_MASK                                                        (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_7_DEV_NACK_RETRY_CNT_LOW                                              (29)
`define I3CCSR_DAT_DAT_MEMORY_7_DEV_NACK_RETRY_CNT_MASK                                             (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_7_DEVICE_LOW                                                          (31)
`define I3CCSR_DAT_DAT_MEMORY_7_DEVICE_MASK                                                         (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_7_AUTOCMD_MASK_LOW                                                    (32)
`define I3CCSR_DAT_DAT_MEMORY_7_AUTOCMD_MASK_MASK                                                   (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_7_AUTOCMD_VALUE_LOW                                                   (40)
`define I3CCSR_DAT_DAT_MEMORY_7_AUTOCMD_VALUE_MASK                                                  (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_7_AUTOCMD_MODE_LOW                                                    (48)
`define I3CCSR_DAT_DAT_MEMORY_7_AUTOCMD_MODE_MASK                                                   (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_7_AUTOCMD_HDR_CODE_LOW                                                (51)
`define I3CCSR_DAT_DAT_MEMORY_7_AUTOCMD_HDR_CODE_MASK                                               (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_8
`define I3CCSR_DAT_DAT_MEMORY_8                                                                     (32'h40)
`define I3CCSR_DAT_DAT_MEMORY_8_STATIC_ADDRESS_LOW                                                  (0)
`define I3CCSR_DAT_DAT_MEMORY_8_STATIC_ADDRESS_MASK                                                 (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_8_IBI_PAYLOAD_LOW                                                     (12)
`define I3CCSR_DAT_DAT_MEMORY_8_IBI_PAYLOAD_MASK                                                    (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_8_IBI_REJECT_LOW                                                      (13)
`define I3CCSR_DAT_DAT_MEMORY_8_IBI_REJECT_MASK                                                     (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_8_CRR_REJECT_LOW                                                      (14)
`define I3CCSR_DAT_DAT_MEMORY_8_CRR_REJECT_MASK                                                     (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_8_TS_LOW                                                              (15)
`define I3CCSR_DAT_DAT_MEMORY_8_TS_MASK                                                             (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_8_DYNAMIC_ADDRESS_LOW                                                 (16)
`define I3CCSR_DAT_DAT_MEMORY_8_DYNAMIC_ADDRESS_MASK                                                (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_8_RING_ID_LOW                                                         (26)
`define I3CCSR_DAT_DAT_MEMORY_8_RING_ID_MASK                                                        (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_8_DEV_NACK_RETRY_CNT_LOW                                              (29)
`define I3CCSR_DAT_DAT_MEMORY_8_DEV_NACK_RETRY_CNT_MASK                                             (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_8_DEVICE_LOW                                                          (31)
`define I3CCSR_DAT_DAT_MEMORY_8_DEVICE_MASK                                                         (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_8_AUTOCMD_MASK_LOW                                                    (32)
`define I3CCSR_DAT_DAT_MEMORY_8_AUTOCMD_MASK_MASK                                                   (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_8_AUTOCMD_VALUE_LOW                                                   (40)
`define I3CCSR_DAT_DAT_MEMORY_8_AUTOCMD_VALUE_MASK                                                  (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_8_AUTOCMD_MODE_LOW                                                    (48)
`define I3CCSR_DAT_DAT_MEMORY_8_AUTOCMD_MODE_MASK                                                   (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_8_AUTOCMD_HDR_CODE_LOW                                                (51)
`define I3CCSR_DAT_DAT_MEMORY_8_AUTOCMD_HDR_CODE_MASK                                               (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_9
`define I3CCSR_DAT_DAT_MEMORY_9                                                                     (32'h48)
`define I3CCSR_DAT_DAT_MEMORY_9_STATIC_ADDRESS_LOW                                                  (0)
`define I3CCSR_DAT_DAT_MEMORY_9_STATIC_ADDRESS_MASK                                                 (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_9_IBI_PAYLOAD_LOW                                                     (12)
`define I3CCSR_DAT_DAT_MEMORY_9_IBI_PAYLOAD_MASK                                                    (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_9_IBI_REJECT_LOW                                                      (13)
`define I3CCSR_DAT_DAT_MEMORY_9_IBI_REJECT_MASK                                                     (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_9_CRR_REJECT_LOW                                                      (14)
`define I3CCSR_DAT_DAT_MEMORY_9_CRR_REJECT_MASK                                                     (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_9_TS_LOW                                                              (15)
`define I3CCSR_DAT_DAT_MEMORY_9_TS_MASK                                                             (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_9_DYNAMIC_ADDRESS_LOW                                                 (16)
`define I3CCSR_DAT_DAT_MEMORY_9_DYNAMIC_ADDRESS_MASK                                                (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_9_RING_ID_LOW                                                         (26)
`define I3CCSR_DAT_DAT_MEMORY_9_RING_ID_MASK                                                        (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_9_DEV_NACK_RETRY_CNT_LOW                                              (29)
`define I3CCSR_DAT_DAT_MEMORY_9_DEV_NACK_RETRY_CNT_MASK                                             (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_9_DEVICE_LOW                                                          (31)
`define I3CCSR_DAT_DAT_MEMORY_9_DEVICE_MASK                                                         (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_9_AUTOCMD_MASK_LOW                                                    (32)
`define I3CCSR_DAT_DAT_MEMORY_9_AUTOCMD_MASK_MASK                                                   (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_9_AUTOCMD_VALUE_LOW                                                   (40)
`define I3CCSR_DAT_DAT_MEMORY_9_AUTOCMD_VALUE_MASK                                                  (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_9_AUTOCMD_MODE_LOW                                                    (48)
`define I3CCSR_DAT_DAT_MEMORY_9_AUTOCMD_MODE_MASK                                                   (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_9_AUTOCMD_HDR_CODE_LOW                                                (51)
`define I3CCSR_DAT_DAT_MEMORY_9_AUTOCMD_HDR_CODE_MASK                                               (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_10
`define I3CCSR_DAT_DAT_MEMORY_10                                                                    (32'h50)
`define I3CCSR_DAT_DAT_MEMORY_10_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_10_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_10_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_10_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_10_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_10_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_10_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_10_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_10_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_10_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_10_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_10_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_10_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_10_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_10_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_10_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_10_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_10_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_10_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_10_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_10_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_10_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_10_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_10_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_10_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_10_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_11
`define I3CCSR_DAT_DAT_MEMORY_11                                                                    (32'h58)
`define I3CCSR_DAT_DAT_MEMORY_11_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_11_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_11_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_11_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_11_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_11_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_11_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_11_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_11_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_11_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_11_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_11_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_11_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_11_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_11_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_11_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_11_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_11_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_11_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_11_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_11_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_11_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_11_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_11_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_11_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_11_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_12
`define I3CCSR_DAT_DAT_MEMORY_12                                                                    (32'h60)
`define I3CCSR_DAT_DAT_MEMORY_12_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_12_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_12_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_12_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_12_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_12_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_12_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_12_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_12_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_12_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_12_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_12_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_12_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_12_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_12_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_12_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_12_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_12_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_12_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_12_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_12_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_12_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_12_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_12_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_12_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_12_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_13
`define I3CCSR_DAT_DAT_MEMORY_13                                                                    (32'h68)
`define I3CCSR_DAT_DAT_MEMORY_13_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_13_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_13_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_13_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_13_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_13_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_13_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_13_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_13_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_13_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_13_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_13_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_13_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_13_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_13_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_13_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_13_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_13_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_13_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_13_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_13_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_13_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_13_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_13_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_13_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_13_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_14
`define I3CCSR_DAT_DAT_MEMORY_14                                                                    (32'h70)
`define I3CCSR_DAT_DAT_MEMORY_14_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_14_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_14_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_14_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_14_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_14_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_14_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_14_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_14_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_14_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_14_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_14_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_14_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_14_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_14_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_14_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_14_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_14_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_14_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_14_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_14_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_14_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_14_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_14_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_14_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_14_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_15
`define I3CCSR_DAT_DAT_MEMORY_15                                                                    (32'h78)
`define I3CCSR_DAT_DAT_MEMORY_15_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_15_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_15_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_15_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_15_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_15_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_15_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_15_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_15_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_15_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_15_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_15_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_15_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_15_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_15_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_15_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_15_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_15_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_15_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_15_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_15_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_15_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_15_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_15_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_15_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_15_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_16
`define I3CCSR_DAT_DAT_MEMORY_16                                                                    (32'h80)
`define I3CCSR_DAT_DAT_MEMORY_16_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_16_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_16_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_16_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_16_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_16_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_16_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_16_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_16_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_16_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_16_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_16_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_16_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_16_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_16_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_16_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_16_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_16_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_16_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_16_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_16_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_16_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_16_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_16_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_16_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_16_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_17
`define I3CCSR_DAT_DAT_MEMORY_17                                                                    (32'h88)
`define I3CCSR_DAT_DAT_MEMORY_17_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_17_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_17_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_17_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_17_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_17_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_17_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_17_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_17_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_17_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_17_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_17_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_17_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_17_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_17_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_17_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_17_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_17_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_17_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_17_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_17_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_17_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_17_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_17_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_17_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_17_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_18
`define I3CCSR_DAT_DAT_MEMORY_18                                                                    (32'h90)
`define I3CCSR_DAT_DAT_MEMORY_18_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_18_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_18_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_18_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_18_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_18_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_18_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_18_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_18_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_18_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_18_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_18_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_18_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_18_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_18_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_18_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_18_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_18_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_18_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_18_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_18_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_18_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_18_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_18_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_18_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_18_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_19
`define I3CCSR_DAT_DAT_MEMORY_19                                                                    (32'h98)
`define I3CCSR_DAT_DAT_MEMORY_19_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_19_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_19_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_19_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_19_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_19_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_19_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_19_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_19_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_19_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_19_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_19_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_19_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_19_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_19_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_19_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_19_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_19_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_19_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_19_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_19_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_19_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_19_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_19_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_19_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_19_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_20
`define I3CCSR_DAT_DAT_MEMORY_20                                                                    (32'ha0)
`define I3CCSR_DAT_DAT_MEMORY_20_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_20_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_20_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_20_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_20_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_20_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_20_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_20_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_20_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_20_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_20_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_20_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_20_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_20_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_20_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_20_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_20_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_20_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_20_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_20_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_20_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_20_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_20_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_20_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_20_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_20_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_21
`define I3CCSR_DAT_DAT_MEMORY_21                                                                    (32'ha8)
`define I3CCSR_DAT_DAT_MEMORY_21_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_21_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_21_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_21_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_21_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_21_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_21_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_21_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_21_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_21_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_21_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_21_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_21_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_21_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_21_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_21_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_21_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_21_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_21_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_21_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_21_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_21_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_21_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_21_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_21_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_21_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_22
`define I3CCSR_DAT_DAT_MEMORY_22                                                                    (32'hb0)
`define I3CCSR_DAT_DAT_MEMORY_22_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_22_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_22_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_22_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_22_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_22_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_22_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_22_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_22_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_22_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_22_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_22_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_22_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_22_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_22_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_22_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_22_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_22_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_22_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_22_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_22_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_22_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_22_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_22_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_22_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_22_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_23
`define I3CCSR_DAT_DAT_MEMORY_23                                                                    (32'hb8)
`define I3CCSR_DAT_DAT_MEMORY_23_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_23_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_23_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_23_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_23_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_23_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_23_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_23_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_23_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_23_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_23_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_23_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_23_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_23_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_23_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_23_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_23_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_23_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_23_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_23_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_23_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_23_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_23_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_23_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_23_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_23_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_24
`define I3CCSR_DAT_DAT_MEMORY_24                                                                    (32'hc0)
`define I3CCSR_DAT_DAT_MEMORY_24_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_24_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_24_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_24_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_24_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_24_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_24_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_24_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_24_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_24_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_24_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_24_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_24_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_24_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_24_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_24_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_24_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_24_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_24_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_24_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_24_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_24_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_24_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_24_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_24_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_24_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_25
`define I3CCSR_DAT_DAT_MEMORY_25                                                                    (32'hc8)
`define I3CCSR_DAT_DAT_MEMORY_25_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_25_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_25_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_25_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_25_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_25_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_25_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_25_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_25_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_25_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_25_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_25_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_25_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_25_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_25_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_25_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_25_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_25_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_25_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_25_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_25_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_25_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_25_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_25_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_25_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_25_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_26
`define I3CCSR_DAT_DAT_MEMORY_26                                                                    (32'hd0)
`define I3CCSR_DAT_DAT_MEMORY_26_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_26_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_26_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_26_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_26_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_26_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_26_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_26_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_26_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_26_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_26_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_26_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_26_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_26_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_26_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_26_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_26_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_26_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_26_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_26_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_26_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_26_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_26_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_26_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_26_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_26_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_27
`define I3CCSR_DAT_DAT_MEMORY_27                                                                    (32'hd8)
`define I3CCSR_DAT_DAT_MEMORY_27_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_27_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_27_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_27_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_27_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_27_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_27_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_27_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_27_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_27_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_27_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_27_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_27_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_27_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_27_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_27_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_27_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_27_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_27_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_27_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_27_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_27_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_27_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_27_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_27_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_27_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_28
`define I3CCSR_DAT_DAT_MEMORY_28                                                                    (32'he0)
`define I3CCSR_DAT_DAT_MEMORY_28_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_28_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_28_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_28_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_28_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_28_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_28_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_28_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_28_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_28_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_28_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_28_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_28_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_28_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_28_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_28_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_28_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_28_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_28_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_28_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_28_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_28_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_28_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_28_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_28_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_28_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_29
`define I3CCSR_DAT_DAT_MEMORY_29                                                                    (32'he8)
`define I3CCSR_DAT_DAT_MEMORY_29_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_29_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_29_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_29_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_29_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_29_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_29_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_29_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_29_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_29_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_29_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_29_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_29_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_29_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_29_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_29_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_29_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_29_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_29_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_29_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_29_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_29_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_29_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_29_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_29_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_29_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_30
`define I3CCSR_DAT_DAT_MEMORY_30                                                                    (32'hf0)
`define I3CCSR_DAT_DAT_MEMORY_30_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_30_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_30_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_30_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_30_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_30_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_30_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_30_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_30_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_30_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_30_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_30_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_30_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_30_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_30_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_30_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_30_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_30_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_30_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_30_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_30_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_30_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_30_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_30_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_30_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_30_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_31
`define I3CCSR_DAT_DAT_MEMORY_31                                                                    (32'hf8)
`define I3CCSR_DAT_DAT_MEMORY_31_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_31_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_31_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_31_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_31_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_31_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_31_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_31_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_31_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_31_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_31_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_31_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_31_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_31_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_31_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_31_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_31_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_31_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_31_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_31_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_31_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_31_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_31_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_31_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_31_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_31_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_32
`define I3CCSR_DAT_DAT_MEMORY_32                                                                    (32'h100)
`define I3CCSR_DAT_DAT_MEMORY_32_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_32_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_32_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_32_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_32_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_32_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_32_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_32_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_32_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_32_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_32_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_32_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_32_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_32_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_32_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_32_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_32_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_32_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_32_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_32_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_32_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_32_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_32_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_32_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_32_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_32_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_33
`define I3CCSR_DAT_DAT_MEMORY_33                                                                    (32'h108)
`define I3CCSR_DAT_DAT_MEMORY_33_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_33_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_33_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_33_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_33_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_33_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_33_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_33_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_33_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_33_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_33_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_33_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_33_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_33_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_33_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_33_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_33_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_33_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_33_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_33_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_33_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_33_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_33_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_33_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_33_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_33_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_34
`define I3CCSR_DAT_DAT_MEMORY_34                                                                    (32'h110)
`define I3CCSR_DAT_DAT_MEMORY_34_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_34_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_34_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_34_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_34_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_34_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_34_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_34_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_34_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_34_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_34_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_34_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_34_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_34_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_34_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_34_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_34_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_34_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_34_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_34_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_34_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_34_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_34_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_34_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_34_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_34_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_35
`define I3CCSR_DAT_DAT_MEMORY_35                                                                    (32'h118)
`define I3CCSR_DAT_DAT_MEMORY_35_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_35_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_35_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_35_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_35_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_35_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_35_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_35_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_35_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_35_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_35_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_35_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_35_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_35_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_35_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_35_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_35_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_35_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_35_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_35_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_35_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_35_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_35_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_35_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_35_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_35_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_36
`define I3CCSR_DAT_DAT_MEMORY_36                                                                    (32'h120)
`define I3CCSR_DAT_DAT_MEMORY_36_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_36_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_36_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_36_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_36_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_36_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_36_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_36_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_36_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_36_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_36_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_36_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_36_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_36_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_36_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_36_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_36_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_36_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_36_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_36_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_36_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_36_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_36_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_36_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_36_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_36_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_37
`define I3CCSR_DAT_DAT_MEMORY_37                                                                    (32'h128)
`define I3CCSR_DAT_DAT_MEMORY_37_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_37_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_37_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_37_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_37_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_37_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_37_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_37_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_37_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_37_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_37_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_37_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_37_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_37_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_37_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_37_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_37_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_37_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_37_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_37_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_37_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_37_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_37_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_37_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_37_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_37_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_38
`define I3CCSR_DAT_DAT_MEMORY_38                                                                    (32'h130)
`define I3CCSR_DAT_DAT_MEMORY_38_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_38_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_38_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_38_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_38_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_38_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_38_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_38_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_38_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_38_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_38_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_38_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_38_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_38_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_38_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_38_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_38_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_38_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_38_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_38_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_38_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_38_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_38_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_38_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_38_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_38_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_39
`define I3CCSR_DAT_DAT_MEMORY_39                                                                    (32'h138)
`define I3CCSR_DAT_DAT_MEMORY_39_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_39_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_39_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_39_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_39_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_39_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_39_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_39_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_39_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_39_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_39_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_39_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_39_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_39_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_39_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_39_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_39_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_39_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_39_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_39_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_39_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_39_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_39_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_39_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_39_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_39_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_40
`define I3CCSR_DAT_DAT_MEMORY_40                                                                    (32'h140)
`define I3CCSR_DAT_DAT_MEMORY_40_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_40_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_40_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_40_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_40_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_40_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_40_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_40_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_40_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_40_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_40_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_40_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_40_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_40_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_40_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_40_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_40_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_40_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_40_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_40_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_40_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_40_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_40_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_40_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_40_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_40_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_41
`define I3CCSR_DAT_DAT_MEMORY_41                                                                    (32'h148)
`define I3CCSR_DAT_DAT_MEMORY_41_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_41_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_41_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_41_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_41_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_41_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_41_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_41_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_41_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_41_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_41_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_41_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_41_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_41_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_41_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_41_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_41_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_41_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_41_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_41_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_41_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_41_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_41_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_41_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_41_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_41_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_42
`define I3CCSR_DAT_DAT_MEMORY_42                                                                    (32'h150)
`define I3CCSR_DAT_DAT_MEMORY_42_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_42_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_42_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_42_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_42_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_42_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_42_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_42_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_42_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_42_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_42_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_42_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_42_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_42_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_42_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_42_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_42_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_42_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_42_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_42_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_42_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_42_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_42_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_42_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_42_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_42_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_43
`define I3CCSR_DAT_DAT_MEMORY_43                                                                    (32'h158)
`define I3CCSR_DAT_DAT_MEMORY_43_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_43_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_43_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_43_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_43_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_43_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_43_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_43_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_43_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_43_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_43_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_43_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_43_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_43_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_43_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_43_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_43_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_43_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_43_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_43_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_43_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_43_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_43_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_43_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_43_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_43_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_44
`define I3CCSR_DAT_DAT_MEMORY_44                                                                    (32'h160)
`define I3CCSR_DAT_DAT_MEMORY_44_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_44_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_44_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_44_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_44_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_44_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_44_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_44_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_44_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_44_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_44_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_44_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_44_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_44_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_44_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_44_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_44_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_44_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_44_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_44_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_44_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_44_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_44_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_44_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_44_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_44_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_45
`define I3CCSR_DAT_DAT_MEMORY_45                                                                    (32'h168)
`define I3CCSR_DAT_DAT_MEMORY_45_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_45_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_45_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_45_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_45_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_45_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_45_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_45_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_45_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_45_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_45_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_45_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_45_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_45_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_45_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_45_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_45_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_45_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_45_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_45_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_45_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_45_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_45_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_45_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_45_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_45_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_46
`define I3CCSR_DAT_DAT_MEMORY_46                                                                    (32'h170)
`define I3CCSR_DAT_DAT_MEMORY_46_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_46_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_46_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_46_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_46_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_46_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_46_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_46_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_46_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_46_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_46_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_46_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_46_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_46_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_46_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_46_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_46_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_46_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_46_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_46_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_46_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_46_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_46_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_46_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_46_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_46_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_47
`define I3CCSR_DAT_DAT_MEMORY_47                                                                    (32'h178)
`define I3CCSR_DAT_DAT_MEMORY_47_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_47_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_47_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_47_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_47_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_47_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_47_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_47_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_47_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_47_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_47_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_47_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_47_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_47_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_47_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_47_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_47_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_47_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_47_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_47_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_47_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_47_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_47_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_47_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_47_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_47_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_48
`define I3CCSR_DAT_DAT_MEMORY_48                                                                    (32'h180)
`define I3CCSR_DAT_DAT_MEMORY_48_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_48_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_48_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_48_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_48_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_48_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_48_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_48_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_48_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_48_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_48_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_48_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_48_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_48_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_48_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_48_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_48_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_48_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_48_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_48_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_48_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_48_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_48_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_48_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_48_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_48_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_49
`define I3CCSR_DAT_DAT_MEMORY_49                                                                    (32'h188)
`define I3CCSR_DAT_DAT_MEMORY_49_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_49_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_49_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_49_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_49_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_49_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_49_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_49_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_49_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_49_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_49_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_49_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_49_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_49_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_49_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_49_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_49_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_49_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_49_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_49_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_49_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_49_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_49_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_49_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_49_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_49_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_50
`define I3CCSR_DAT_DAT_MEMORY_50                                                                    (32'h190)
`define I3CCSR_DAT_DAT_MEMORY_50_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_50_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_50_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_50_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_50_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_50_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_50_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_50_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_50_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_50_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_50_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_50_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_50_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_50_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_50_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_50_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_50_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_50_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_50_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_50_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_50_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_50_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_50_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_50_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_50_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_50_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_51
`define I3CCSR_DAT_DAT_MEMORY_51                                                                    (32'h198)
`define I3CCSR_DAT_DAT_MEMORY_51_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_51_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_51_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_51_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_51_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_51_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_51_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_51_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_51_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_51_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_51_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_51_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_51_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_51_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_51_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_51_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_51_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_51_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_51_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_51_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_51_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_51_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_51_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_51_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_51_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_51_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_52
`define I3CCSR_DAT_DAT_MEMORY_52                                                                    (32'h1a0)
`define I3CCSR_DAT_DAT_MEMORY_52_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_52_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_52_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_52_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_52_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_52_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_52_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_52_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_52_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_52_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_52_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_52_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_52_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_52_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_52_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_52_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_52_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_52_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_52_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_52_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_52_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_52_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_52_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_52_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_52_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_52_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_53
`define I3CCSR_DAT_DAT_MEMORY_53                                                                    (32'h1a8)
`define I3CCSR_DAT_DAT_MEMORY_53_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_53_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_53_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_53_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_53_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_53_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_53_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_53_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_53_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_53_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_53_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_53_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_53_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_53_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_53_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_53_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_53_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_53_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_53_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_53_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_53_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_53_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_53_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_53_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_53_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_53_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_54
`define I3CCSR_DAT_DAT_MEMORY_54                                                                    (32'h1b0)
`define I3CCSR_DAT_DAT_MEMORY_54_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_54_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_54_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_54_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_54_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_54_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_54_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_54_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_54_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_54_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_54_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_54_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_54_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_54_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_54_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_54_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_54_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_54_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_54_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_54_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_54_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_54_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_54_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_54_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_54_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_54_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_55
`define I3CCSR_DAT_DAT_MEMORY_55                                                                    (32'h1b8)
`define I3CCSR_DAT_DAT_MEMORY_55_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_55_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_55_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_55_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_55_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_55_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_55_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_55_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_55_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_55_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_55_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_55_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_55_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_55_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_55_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_55_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_55_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_55_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_55_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_55_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_55_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_55_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_55_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_55_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_55_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_55_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_56
`define I3CCSR_DAT_DAT_MEMORY_56                                                                    (32'h1c0)
`define I3CCSR_DAT_DAT_MEMORY_56_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_56_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_56_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_56_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_56_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_56_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_56_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_56_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_56_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_56_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_56_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_56_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_56_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_56_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_56_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_56_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_56_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_56_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_56_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_56_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_56_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_56_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_56_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_56_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_56_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_56_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_57
`define I3CCSR_DAT_DAT_MEMORY_57                                                                    (32'h1c8)
`define I3CCSR_DAT_DAT_MEMORY_57_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_57_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_57_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_57_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_57_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_57_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_57_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_57_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_57_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_57_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_57_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_57_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_57_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_57_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_57_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_57_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_57_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_57_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_57_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_57_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_57_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_57_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_57_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_57_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_57_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_57_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_58
`define I3CCSR_DAT_DAT_MEMORY_58                                                                    (32'h1d0)
`define I3CCSR_DAT_DAT_MEMORY_58_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_58_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_58_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_58_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_58_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_58_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_58_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_58_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_58_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_58_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_58_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_58_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_58_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_58_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_58_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_58_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_58_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_58_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_58_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_58_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_58_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_58_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_58_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_58_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_58_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_58_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_59
`define I3CCSR_DAT_DAT_MEMORY_59                                                                    (32'h1d8)
`define I3CCSR_DAT_DAT_MEMORY_59_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_59_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_59_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_59_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_59_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_59_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_59_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_59_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_59_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_59_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_59_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_59_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_59_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_59_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_59_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_59_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_59_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_59_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_59_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_59_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_59_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_59_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_59_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_59_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_59_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_59_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_60
`define I3CCSR_DAT_DAT_MEMORY_60                                                                    (32'h1e0)
`define I3CCSR_DAT_DAT_MEMORY_60_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_60_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_60_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_60_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_60_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_60_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_60_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_60_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_60_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_60_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_60_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_60_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_60_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_60_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_60_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_60_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_60_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_60_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_60_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_60_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_60_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_60_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_60_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_60_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_60_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_60_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_61
`define I3CCSR_DAT_DAT_MEMORY_61                                                                    (32'h1e8)
`define I3CCSR_DAT_DAT_MEMORY_61_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_61_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_61_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_61_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_61_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_61_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_61_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_61_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_61_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_61_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_61_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_61_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_61_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_61_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_61_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_61_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_61_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_61_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_61_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_61_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_61_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_61_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_61_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_61_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_61_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_61_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_62
`define I3CCSR_DAT_DAT_MEMORY_62                                                                    (32'h1f0)
`define I3CCSR_DAT_DAT_MEMORY_62_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_62_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_62_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_62_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_62_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_62_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_62_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_62_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_62_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_62_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_62_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_62_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_62_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_62_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_62_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_62_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_62_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_62_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_62_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_62_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_62_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_62_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_62_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_62_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_62_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_62_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_63
`define I3CCSR_DAT_DAT_MEMORY_63                                                                    (32'h1f8)
`define I3CCSR_DAT_DAT_MEMORY_63_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_63_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_63_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_63_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_63_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_63_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_63_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_63_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_63_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_63_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_63_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_63_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_63_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_63_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_63_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_63_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_63_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_63_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_63_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_63_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_63_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_63_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_63_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_63_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_63_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_63_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_64
`define I3CCSR_DAT_DAT_MEMORY_64                                                                    (32'h200)
`define I3CCSR_DAT_DAT_MEMORY_64_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_64_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_64_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_64_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_64_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_64_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_64_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_64_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_64_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_64_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_64_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_64_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_64_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_64_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_64_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_64_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_64_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_64_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_64_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_64_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_64_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_64_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_64_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_64_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_64_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_64_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_65
`define I3CCSR_DAT_DAT_MEMORY_65                                                                    (32'h208)
`define I3CCSR_DAT_DAT_MEMORY_65_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_65_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_65_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_65_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_65_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_65_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_65_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_65_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_65_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_65_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_65_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_65_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_65_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_65_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_65_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_65_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_65_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_65_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_65_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_65_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_65_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_65_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_65_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_65_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_65_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_65_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_66
`define I3CCSR_DAT_DAT_MEMORY_66                                                                    (32'h210)
`define I3CCSR_DAT_DAT_MEMORY_66_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_66_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_66_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_66_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_66_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_66_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_66_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_66_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_66_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_66_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_66_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_66_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_66_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_66_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_66_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_66_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_66_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_66_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_66_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_66_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_66_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_66_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_66_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_66_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_66_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_66_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_67
`define I3CCSR_DAT_DAT_MEMORY_67                                                                    (32'h218)
`define I3CCSR_DAT_DAT_MEMORY_67_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_67_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_67_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_67_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_67_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_67_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_67_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_67_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_67_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_67_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_67_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_67_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_67_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_67_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_67_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_67_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_67_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_67_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_67_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_67_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_67_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_67_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_67_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_67_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_67_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_67_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_68
`define I3CCSR_DAT_DAT_MEMORY_68                                                                    (32'h220)
`define I3CCSR_DAT_DAT_MEMORY_68_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_68_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_68_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_68_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_68_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_68_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_68_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_68_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_68_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_68_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_68_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_68_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_68_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_68_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_68_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_68_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_68_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_68_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_68_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_68_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_68_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_68_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_68_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_68_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_68_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_68_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_69
`define I3CCSR_DAT_DAT_MEMORY_69                                                                    (32'h228)
`define I3CCSR_DAT_DAT_MEMORY_69_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_69_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_69_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_69_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_69_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_69_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_69_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_69_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_69_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_69_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_69_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_69_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_69_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_69_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_69_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_69_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_69_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_69_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_69_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_69_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_69_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_69_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_69_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_69_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_69_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_69_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_70
`define I3CCSR_DAT_DAT_MEMORY_70                                                                    (32'h230)
`define I3CCSR_DAT_DAT_MEMORY_70_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_70_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_70_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_70_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_70_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_70_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_70_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_70_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_70_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_70_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_70_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_70_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_70_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_70_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_70_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_70_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_70_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_70_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_70_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_70_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_70_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_70_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_70_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_70_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_70_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_70_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_71
`define I3CCSR_DAT_DAT_MEMORY_71                                                                    (32'h238)
`define I3CCSR_DAT_DAT_MEMORY_71_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_71_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_71_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_71_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_71_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_71_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_71_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_71_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_71_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_71_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_71_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_71_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_71_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_71_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_71_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_71_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_71_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_71_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_71_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_71_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_71_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_71_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_71_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_71_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_71_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_71_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_72
`define I3CCSR_DAT_DAT_MEMORY_72                                                                    (32'h240)
`define I3CCSR_DAT_DAT_MEMORY_72_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_72_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_72_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_72_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_72_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_72_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_72_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_72_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_72_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_72_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_72_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_72_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_72_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_72_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_72_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_72_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_72_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_72_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_72_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_72_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_72_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_72_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_72_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_72_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_72_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_72_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_73
`define I3CCSR_DAT_DAT_MEMORY_73                                                                    (32'h248)
`define I3CCSR_DAT_DAT_MEMORY_73_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_73_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_73_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_73_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_73_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_73_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_73_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_73_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_73_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_73_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_73_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_73_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_73_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_73_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_73_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_73_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_73_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_73_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_73_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_73_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_73_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_73_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_73_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_73_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_73_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_73_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_74
`define I3CCSR_DAT_DAT_MEMORY_74                                                                    (32'h250)
`define I3CCSR_DAT_DAT_MEMORY_74_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_74_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_74_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_74_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_74_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_74_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_74_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_74_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_74_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_74_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_74_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_74_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_74_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_74_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_74_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_74_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_74_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_74_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_74_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_74_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_74_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_74_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_74_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_74_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_74_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_74_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_75
`define I3CCSR_DAT_DAT_MEMORY_75                                                                    (32'h258)
`define I3CCSR_DAT_DAT_MEMORY_75_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_75_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_75_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_75_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_75_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_75_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_75_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_75_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_75_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_75_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_75_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_75_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_75_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_75_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_75_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_75_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_75_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_75_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_75_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_75_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_75_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_75_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_75_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_75_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_75_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_75_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_76
`define I3CCSR_DAT_DAT_MEMORY_76                                                                    (32'h260)
`define I3CCSR_DAT_DAT_MEMORY_76_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_76_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_76_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_76_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_76_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_76_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_76_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_76_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_76_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_76_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_76_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_76_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_76_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_76_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_76_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_76_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_76_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_76_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_76_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_76_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_76_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_76_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_76_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_76_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_76_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_76_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_77
`define I3CCSR_DAT_DAT_MEMORY_77                                                                    (32'h268)
`define I3CCSR_DAT_DAT_MEMORY_77_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_77_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_77_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_77_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_77_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_77_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_77_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_77_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_77_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_77_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_77_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_77_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_77_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_77_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_77_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_77_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_77_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_77_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_77_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_77_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_77_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_77_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_77_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_77_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_77_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_77_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_78
`define I3CCSR_DAT_DAT_MEMORY_78                                                                    (32'h270)
`define I3CCSR_DAT_DAT_MEMORY_78_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_78_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_78_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_78_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_78_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_78_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_78_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_78_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_78_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_78_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_78_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_78_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_78_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_78_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_78_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_78_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_78_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_78_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_78_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_78_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_78_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_78_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_78_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_78_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_78_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_78_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_79
`define I3CCSR_DAT_DAT_MEMORY_79                                                                    (32'h278)
`define I3CCSR_DAT_DAT_MEMORY_79_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_79_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_79_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_79_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_79_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_79_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_79_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_79_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_79_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_79_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_79_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_79_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_79_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_79_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_79_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_79_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_79_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_79_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_79_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_79_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_79_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_79_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_79_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_79_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_79_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_79_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_80
`define I3CCSR_DAT_DAT_MEMORY_80                                                                    (32'h280)
`define I3CCSR_DAT_DAT_MEMORY_80_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_80_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_80_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_80_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_80_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_80_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_80_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_80_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_80_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_80_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_80_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_80_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_80_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_80_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_80_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_80_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_80_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_80_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_80_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_80_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_80_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_80_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_80_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_80_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_80_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_80_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_81
`define I3CCSR_DAT_DAT_MEMORY_81                                                                    (32'h288)
`define I3CCSR_DAT_DAT_MEMORY_81_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_81_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_81_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_81_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_81_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_81_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_81_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_81_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_81_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_81_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_81_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_81_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_81_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_81_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_81_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_81_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_81_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_81_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_81_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_81_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_81_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_81_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_81_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_81_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_81_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_81_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_82
`define I3CCSR_DAT_DAT_MEMORY_82                                                                    (32'h290)
`define I3CCSR_DAT_DAT_MEMORY_82_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_82_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_82_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_82_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_82_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_82_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_82_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_82_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_82_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_82_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_82_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_82_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_82_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_82_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_82_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_82_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_82_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_82_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_82_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_82_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_82_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_82_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_82_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_82_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_82_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_82_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_83
`define I3CCSR_DAT_DAT_MEMORY_83                                                                    (32'h298)
`define I3CCSR_DAT_DAT_MEMORY_83_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_83_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_83_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_83_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_83_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_83_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_83_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_83_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_83_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_83_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_83_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_83_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_83_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_83_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_83_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_83_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_83_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_83_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_83_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_83_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_83_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_83_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_83_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_83_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_83_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_83_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_84
`define I3CCSR_DAT_DAT_MEMORY_84                                                                    (32'h2a0)
`define I3CCSR_DAT_DAT_MEMORY_84_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_84_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_84_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_84_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_84_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_84_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_84_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_84_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_84_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_84_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_84_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_84_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_84_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_84_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_84_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_84_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_84_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_84_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_84_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_84_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_84_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_84_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_84_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_84_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_84_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_84_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_85
`define I3CCSR_DAT_DAT_MEMORY_85                                                                    (32'h2a8)
`define I3CCSR_DAT_DAT_MEMORY_85_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_85_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_85_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_85_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_85_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_85_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_85_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_85_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_85_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_85_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_85_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_85_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_85_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_85_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_85_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_85_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_85_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_85_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_85_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_85_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_85_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_85_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_85_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_85_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_85_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_85_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_86
`define I3CCSR_DAT_DAT_MEMORY_86                                                                    (32'h2b0)
`define I3CCSR_DAT_DAT_MEMORY_86_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_86_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_86_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_86_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_86_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_86_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_86_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_86_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_86_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_86_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_86_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_86_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_86_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_86_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_86_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_86_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_86_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_86_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_86_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_86_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_86_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_86_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_86_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_86_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_86_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_86_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_87
`define I3CCSR_DAT_DAT_MEMORY_87                                                                    (32'h2b8)
`define I3CCSR_DAT_DAT_MEMORY_87_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_87_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_87_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_87_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_87_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_87_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_87_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_87_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_87_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_87_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_87_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_87_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_87_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_87_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_87_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_87_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_87_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_87_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_87_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_87_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_87_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_87_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_87_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_87_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_87_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_87_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_88
`define I3CCSR_DAT_DAT_MEMORY_88                                                                    (32'h2c0)
`define I3CCSR_DAT_DAT_MEMORY_88_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_88_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_88_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_88_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_88_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_88_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_88_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_88_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_88_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_88_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_88_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_88_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_88_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_88_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_88_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_88_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_88_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_88_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_88_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_88_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_88_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_88_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_88_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_88_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_88_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_88_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_89
`define I3CCSR_DAT_DAT_MEMORY_89                                                                    (32'h2c8)
`define I3CCSR_DAT_DAT_MEMORY_89_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_89_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_89_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_89_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_89_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_89_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_89_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_89_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_89_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_89_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_89_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_89_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_89_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_89_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_89_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_89_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_89_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_89_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_89_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_89_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_89_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_89_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_89_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_89_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_89_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_89_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_90
`define I3CCSR_DAT_DAT_MEMORY_90                                                                    (32'h2d0)
`define I3CCSR_DAT_DAT_MEMORY_90_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_90_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_90_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_90_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_90_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_90_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_90_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_90_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_90_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_90_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_90_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_90_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_90_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_90_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_90_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_90_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_90_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_90_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_90_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_90_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_90_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_90_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_90_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_90_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_90_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_90_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_91
`define I3CCSR_DAT_DAT_MEMORY_91                                                                    (32'h2d8)
`define I3CCSR_DAT_DAT_MEMORY_91_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_91_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_91_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_91_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_91_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_91_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_91_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_91_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_91_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_91_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_91_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_91_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_91_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_91_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_91_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_91_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_91_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_91_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_91_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_91_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_91_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_91_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_91_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_91_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_91_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_91_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_92
`define I3CCSR_DAT_DAT_MEMORY_92                                                                    (32'h2e0)
`define I3CCSR_DAT_DAT_MEMORY_92_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_92_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_92_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_92_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_92_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_92_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_92_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_92_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_92_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_92_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_92_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_92_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_92_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_92_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_92_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_92_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_92_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_92_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_92_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_92_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_92_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_92_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_92_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_92_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_92_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_92_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_93
`define I3CCSR_DAT_DAT_MEMORY_93                                                                    (32'h2e8)
`define I3CCSR_DAT_DAT_MEMORY_93_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_93_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_93_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_93_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_93_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_93_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_93_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_93_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_93_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_93_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_93_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_93_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_93_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_93_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_93_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_93_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_93_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_93_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_93_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_93_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_93_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_93_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_93_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_93_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_93_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_93_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_94
`define I3CCSR_DAT_DAT_MEMORY_94                                                                    (32'h2f0)
`define I3CCSR_DAT_DAT_MEMORY_94_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_94_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_94_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_94_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_94_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_94_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_94_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_94_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_94_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_94_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_94_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_94_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_94_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_94_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_94_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_94_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_94_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_94_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_94_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_94_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_94_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_94_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_94_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_94_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_94_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_94_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_95
`define I3CCSR_DAT_DAT_MEMORY_95                                                                    (32'h2f8)
`define I3CCSR_DAT_DAT_MEMORY_95_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_95_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_95_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_95_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_95_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_95_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_95_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_95_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_95_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_95_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_95_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_95_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_95_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_95_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_95_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_95_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_95_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_95_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_95_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_95_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_95_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_95_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_95_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_95_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_95_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_95_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_96
`define I3CCSR_DAT_DAT_MEMORY_96                                                                    (32'h300)
`define I3CCSR_DAT_DAT_MEMORY_96_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_96_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_96_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_96_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_96_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_96_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_96_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_96_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_96_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_96_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_96_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_96_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_96_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_96_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_96_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_96_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_96_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_96_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_96_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_96_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_96_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_96_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_96_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_96_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_96_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_96_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_97
`define I3CCSR_DAT_DAT_MEMORY_97                                                                    (32'h308)
`define I3CCSR_DAT_DAT_MEMORY_97_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_97_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_97_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_97_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_97_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_97_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_97_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_97_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_97_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_97_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_97_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_97_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_97_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_97_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_97_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_97_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_97_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_97_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_97_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_97_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_97_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_97_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_97_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_97_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_97_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_97_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_98
`define I3CCSR_DAT_DAT_MEMORY_98                                                                    (32'h310)
`define I3CCSR_DAT_DAT_MEMORY_98_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_98_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_98_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_98_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_98_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_98_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_98_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_98_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_98_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_98_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_98_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_98_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_98_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_98_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_98_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_98_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_98_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_98_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_98_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_98_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_98_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_98_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_98_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_98_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_98_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_98_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_99
`define I3CCSR_DAT_DAT_MEMORY_99                                                                    (32'h318)
`define I3CCSR_DAT_DAT_MEMORY_99_STATIC_ADDRESS_LOW                                                 (0)
`define I3CCSR_DAT_DAT_MEMORY_99_STATIC_ADDRESS_MASK                                                (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_99_IBI_PAYLOAD_LOW                                                    (12)
`define I3CCSR_DAT_DAT_MEMORY_99_IBI_PAYLOAD_MASK                                                   (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_99_IBI_REJECT_LOW                                                     (13)
`define I3CCSR_DAT_DAT_MEMORY_99_IBI_REJECT_MASK                                                    (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_99_CRR_REJECT_LOW                                                     (14)
`define I3CCSR_DAT_DAT_MEMORY_99_CRR_REJECT_MASK                                                    (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_99_TS_LOW                                                             (15)
`define I3CCSR_DAT_DAT_MEMORY_99_TS_MASK                                                            (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_99_DYNAMIC_ADDRESS_LOW                                                (16)
`define I3CCSR_DAT_DAT_MEMORY_99_DYNAMIC_ADDRESS_MASK                                               (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_99_RING_ID_LOW                                                        (26)
`define I3CCSR_DAT_DAT_MEMORY_99_RING_ID_MASK                                                       (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_99_DEV_NACK_RETRY_CNT_LOW                                             (29)
`define I3CCSR_DAT_DAT_MEMORY_99_DEV_NACK_RETRY_CNT_MASK                                            (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_99_DEVICE_LOW                                                         (31)
`define I3CCSR_DAT_DAT_MEMORY_99_DEVICE_MASK                                                        (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_99_AUTOCMD_MASK_LOW                                                   (32)
`define I3CCSR_DAT_DAT_MEMORY_99_AUTOCMD_MASK_MASK                                                  (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_99_AUTOCMD_VALUE_LOW                                                  (40)
`define I3CCSR_DAT_DAT_MEMORY_99_AUTOCMD_VALUE_MASK                                                 (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_99_AUTOCMD_MODE_LOW                                                   (48)
`define I3CCSR_DAT_DAT_MEMORY_99_AUTOCMD_MODE_MASK                                                  (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_99_AUTOCMD_HDR_CODE_LOW                                               (51)
`define I3CCSR_DAT_DAT_MEMORY_99_AUTOCMD_HDR_CODE_MASK                                              (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_100
`define I3CCSR_DAT_DAT_MEMORY_100                                                                   (32'h320)
`define I3CCSR_DAT_DAT_MEMORY_100_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_100_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_100_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_100_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_100_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_100_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_100_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_100_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_100_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_100_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_100_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_100_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_100_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_100_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_100_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_100_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_100_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_100_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_100_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_100_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_100_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_100_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_100_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_100_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_100_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_100_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_101
`define I3CCSR_DAT_DAT_MEMORY_101                                                                   (32'h328)
`define I3CCSR_DAT_DAT_MEMORY_101_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_101_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_101_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_101_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_101_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_101_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_101_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_101_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_101_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_101_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_101_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_101_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_101_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_101_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_101_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_101_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_101_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_101_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_101_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_101_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_101_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_101_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_101_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_101_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_101_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_101_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_102
`define I3CCSR_DAT_DAT_MEMORY_102                                                                   (32'h330)
`define I3CCSR_DAT_DAT_MEMORY_102_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_102_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_102_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_102_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_102_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_102_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_102_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_102_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_102_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_102_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_102_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_102_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_102_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_102_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_102_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_102_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_102_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_102_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_102_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_102_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_102_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_102_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_102_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_102_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_102_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_102_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_103
`define I3CCSR_DAT_DAT_MEMORY_103                                                                   (32'h338)
`define I3CCSR_DAT_DAT_MEMORY_103_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_103_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_103_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_103_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_103_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_103_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_103_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_103_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_103_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_103_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_103_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_103_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_103_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_103_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_103_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_103_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_103_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_103_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_103_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_103_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_103_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_103_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_103_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_103_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_103_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_103_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_104
`define I3CCSR_DAT_DAT_MEMORY_104                                                                   (32'h340)
`define I3CCSR_DAT_DAT_MEMORY_104_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_104_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_104_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_104_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_104_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_104_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_104_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_104_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_104_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_104_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_104_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_104_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_104_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_104_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_104_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_104_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_104_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_104_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_104_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_104_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_104_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_104_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_104_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_104_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_104_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_104_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_105
`define I3CCSR_DAT_DAT_MEMORY_105                                                                   (32'h348)
`define I3CCSR_DAT_DAT_MEMORY_105_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_105_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_105_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_105_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_105_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_105_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_105_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_105_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_105_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_105_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_105_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_105_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_105_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_105_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_105_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_105_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_105_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_105_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_105_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_105_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_105_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_105_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_105_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_105_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_105_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_105_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_106
`define I3CCSR_DAT_DAT_MEMORY_106                                                                   (32'h350)
`define I3CCSR_DAT_DAT_MEMORY_106_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_106_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_106_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_106_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_106_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_106_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_106_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_106_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_106_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_106_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_106_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_106_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_106_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_106_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_106_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_106_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_106_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_106_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_106_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_106_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_106_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_106_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_106_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_106_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_106_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_106_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_107
`define I3CCSR_DAT_DAT_MEMORY_107                                                                   (32'h358)
`define I3CCSR_DAT_DAT_MEMORY_107_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_107_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_107_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_107_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_107_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_107_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_107_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_107_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_107_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_107_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_107_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_107_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_107_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_107_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_107_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_107_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_107_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_107_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_107_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_107_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_107_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_107_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_107_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_107_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_107_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_107_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_108
`define I3CCSR_DAT_DAT_MEMORY_108                                                                   (32'h360)
`define I3CCSR_DAT_DAT_MEMORY_108_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_108_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_108_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_108_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_108_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_108_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_108_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_108_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_108_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_108_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_108_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_108_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_108_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_108_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_108_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_108_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_108_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_108_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_108_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_108_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_108_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_108_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_108_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_108_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_108_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_108_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_109
`define I3CCSR_DAT_DAT_MEMORY_109                                                                   (32'h368)
`define I3CCSR_DAT_DAT_MEMORY_109_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_109_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_109_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_109_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_109_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_109_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_109_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_109_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_109_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_109_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_109_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_109_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_109_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_109_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_109_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_109_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_109_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_109_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_109_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_109_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_109_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_109_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_109_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_109_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_109_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_109_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_110
`define I3CCSR_DAT_DAT_MEMORY_110                                                                   (32'h370)
`define I3CCSR_DAT_DAT_MEMORY_110_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_110_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_110_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_110_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_110_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_110_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_110_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_110_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_110_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_110_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_110_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_110_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_110_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_110_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_110_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_110_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_110_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_110_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_110_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_110_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_110_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_110_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_110_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_110_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_110_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_110_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_111
`define I3CCSR_DAT_DAT_MEMORY_111                                                                   (32'h378)
`define I3CCSR_DAT_DAT_MEMORY_111_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_111_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_111_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_111_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_111_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_111_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_111_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_111_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_111_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_111_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_111_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_111_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_111_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_111_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_111_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_111_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_111_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_111_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_111_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_111_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_111_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_111_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_111_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_111_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_111_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_111_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_112
`define I3CCSR_DAT_DAT_MEMORY_112                                                                   (32'h380)
`define I3CCSR_DAT_DAT_MEMORY_112_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_112_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_112_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_112_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_112_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_112_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_112_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_112_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_112_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_112_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_112_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_112_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_112_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_112_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_112_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_112_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_112_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_112_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_112_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_112_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_112_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_112_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_112_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_112_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_112_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_112_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_113
`define I3CCSR_DAT_DAT_MEMORY_113                                                                   (32'h388)
`define I3CCSR_DAT_DAT_MEMORY_113_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_113_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_113_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_113_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_113_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_113_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_113_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_113_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_113_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_113_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_113_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_113_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_113_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_113_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_113_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_113_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_113_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_113_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_113_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_113_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_113_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_113_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_113_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_113_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_113_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_113_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_114
`define I3CCSR_DAT_DAT_MEMORY_114                                                                   (32'h390)
`define I3CCSR_DAT_DAT_MEMORY_114_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_114_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_114_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_114_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_114_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_114_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_114_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_114_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_114_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_114_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_114_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_114_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_114_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_114_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_114_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_114_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_114_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_114_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_114_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_114_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_114_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_114_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_114_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_114_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_114_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_114_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_115
`define I3CCSR_DAT_DAT_MEMORY_115                                                                   (32'h398)
`define I3CCSR_DAT_DAT_MEMORY_115_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_115_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_115_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_115_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_115_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_115_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_115_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_115_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_115_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_115_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_115_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_115_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_115_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_115_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_115_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_115_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_115_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_115_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_115_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_115_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_115_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_115_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_115_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_115_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_115_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_115_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_116
`define I3CCSR_DAT_DAT_MEMORY_116                                                                   (32'h3a0)
`define I3CCSR_DAT_DAT_MEMORY_116_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_116_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_116_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_116_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_116_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_116_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_116_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_116_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_116_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_116_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_116_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_116_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_116_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_116_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_116_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_116_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_116_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_116_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_116_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_116_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_116_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_116_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_116_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_116_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_116_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_116_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_117
`define I3CCSR_DAT_DAT_MEMORY_117                                                                   (32'h3a8)
`define I3CCSR_DAT_DAT_MEMORY_117_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_117_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_117_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_117_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_117_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_117_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_117_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_117_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_117_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_117_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_117_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_117_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_117_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_117_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_117_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_117_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_117_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_117_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_117_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_117_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_117_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_117_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_117_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_117_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_117_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_117_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_118
`define I3CCSR_DAT_DAT_MEMORY_118                                                                   (32'h3b0)
`define I3CCSR_DAT_DAT_MEMORY_118_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_118_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_118_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_118_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_118_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_118_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_118_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_118_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_118_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_118_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_118_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_118_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_118_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_118_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_118_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_118_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_118_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_118_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_118_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_118_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_118_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_118_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_118_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_118_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_118_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_118_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_119
`define I3CCSR_DAT_DAT_MEMORY_119                                                                   (32'h3b8)
`define I3CCSR_DAT_DAT_MEMORY_119_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_119_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_119_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_119_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_119_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_119_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_119_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_119_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_119_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_119_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_119_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_119_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_119_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_119_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_119_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_119_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_119_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_119_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_119_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_119_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_119_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_119_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_119_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_119_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_119_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_119_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_120
`define I3CCSR_DAT_DAT_MEMORY_120                                                                   (32'h3c0)
`define I3CCSR_DAT_DAT_MEMORY_120_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_120_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_120_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_120_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_120_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_120_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_120_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_120_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_120_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_120_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_120_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_120_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_120_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_120_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_120_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_120_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_120_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_120_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_120_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_120_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_120_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_120_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_120_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_120_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_120_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_120_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_121
`define I3CCSR_DAT_DAT_MEMORY_121                                                                   (32'h3c8)
`define I3CCSR_DAT_DAT_MEMORY_121_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_121_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_121_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_121_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_121_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_121_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_121_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_121_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_121_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_121_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_121_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_121_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_121_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_121_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_121_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_121_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_121_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_121_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_121_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_121_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_121_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_121_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_121_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_121_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_121_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_121_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_122
`define I3CCSR_DAT_DAT_MEMORY_122                                                                   (32'h3d0)
`define I3CCSR_DAT_DAT_MEMORY_122_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_122_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_122_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_122_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_122_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_122_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_122_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_122_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_122_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_122_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_122_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_122_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_122_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_122_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_122_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_122_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_122_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_122_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_122_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_122_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_122_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_122_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_122_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_122_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_122_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_122_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_123
`define I3CCSR_DAT_DAT_MEMORY_123                                                                   (32'h3d8)
`define I3CCSR_DAT_DAT_MEMORY_123_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_123_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_123_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_123_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_123_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_123_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_123_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_123_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_123_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_123_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_123_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_123_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_123_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_123_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_123_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_123_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_123_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_123_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_123_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_123_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_123_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_123_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_123_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_123_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_123_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_123_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_124
`define I3CCSR_DAT_DAT_MEMORY_124                                                                   (32'h3e0)
`define I3CCSR_DAT_DAT_MEMORY_124_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_124_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_124_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_124_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_124_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_124_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_124_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_124_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_124_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_124_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_124_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_124_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_124_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_124_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_124_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_124_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_124_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_124_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_124_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_124_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_124_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_124_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_124_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_124_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_124_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_124_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_125
`define I3CCSR_DAT_DAT_MEMORY_125                                                                   (32'h3e8)
`define I3CCSR_DAT_DAT_MEMORY_125_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_125_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_125_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_125_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_125_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_125_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_125_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_125_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_125_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_125_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_125_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_125_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_125_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_125_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_125_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_125_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_125_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_125_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_125_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_125_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_125_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_125_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_125_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_125_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_125_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_125_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_126
`define I3CCSR_DAT_DAT_MEMORY_126                                                                   (32'h3f0)
`define I3CCSR_DAT_DAT_MEMORY_126_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_126_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_126_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_126_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_126_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_126_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_126_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_126_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_126_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_126_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_126_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_126_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_126_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_126_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_126_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_126_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_126_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_126_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_126_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_126_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_126_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_126_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_126_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_126_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_126_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_126_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DAT_DAT_MEMORY_127
`define I3CCSR_DAT_DAT_MEMORY_127                                                                   (32'h3f8)
`define I3CCSR_DAT_DAT_MEMORY_127_STATIC_ADDRESS_LOW                                                (0)
`define I3CCSR_DAT_DAT_MEMORY_127_STATIC_ADDRESS_MASK                                               (32'h7f)
`define I3CCSR_DAT_DAT_MEMORY_127_IBI_PAYLOAD_LOW                                                   (12)
`define I3CCSR_DAT_DAT_MEMORY_127_IBI_PAYLOAD_MASK                                                  (32'h1000)
`define I3CCSR_DAT_DAT_MEMORY_127_IBI_REJECT_LOW                                                    (13)
`define I3CCSR_DAT_DAT_MEMORY_127_IBI_REJECT_MASK                                                   (32'h2000)
`define I3CCSR_DAT_DAT_MEMORY_127_CRR_REJECT_LOW                                                    (14)
`define I3CCSR_DAT_DAT_MEMORY_127_CRR_REJECT_MASK                                                   (32'h4000)
`define I3CCSR_DAT_DAT_MEMORY_127_TS_LOW                                                            (15)
`define I3CCSR_DAT_DAT_MEMORY_127_TS_MASK                                                           (32'h8000)
`define I3CCSR_DAT_DAT_MEMORY_127_DYNAMIC_ADDRESS_LOW                                               (16)
`define I3CCSR_DAT_DAT_MEMORY_127_DYNAMIC_ADDRESS_MASK                                              (32'hff0000)
`define I3CCSR_DAT_DAT_MEMORY_127_RING_ID_LOW                                                       (26)
`define I3CCSR_DAT_DAT_MEMORY_127_RING_ID_MASK                                                      (32'h1c000000)
`define I3CCSR_DAT_DAT_MEMORY_127_DEV_NACK_RETRY_CNT_LOW                                            (29)
`define I3CCSR_DAT_DAT_MEMORY_127_DEV_NACK_RETRY_CNT_MASK                                           (32'h60000000)
`define I3CCSR_DAT_DAT_MEMORY_127_DEVICE_LOW                                                        (31)
`define I3CCSR_DAT_DAT_MEMORY_127_DEVICE_MASK                                                       (32'h80000000)
`define I3CCSR_DAT_DAT_MEMORY_127_AUTOCMD_MASK_LOW                                                  (32)
`define I3CCSR_DAT_DAT_MEMORY_127_AUTOCMD_MASK_MASK                                                 (32'hff00000000)
`define I3CCSR_DAT_DAT_MEMORY_127_AUTOCMD_VALUE_LOW                                                 (40)
`define I3CCSR_DAT_DAT_MEMORY_127_AUTOCMD_VALUE_MASK                                                (32'hff0000000000)
`define I3CCSR_DAT_DAT_MEMORY_127_AUTOCMD_MODE_LOW                                                  (48)
`define I3CCSR_DAT_DAT_MEMORY_127_AUTOCMD_MODE_MASK                                                 (32'h7000000000000)
`define I3CCSR_DAT_DAT_MEMORY_127_AUTOCMD_HDR_CODE_LOW                                              (51)
`define I3CCSR_DAT_DAT_MEMORY_127_AUTOCMD_HDR_CODE_MASK                                             (32'h7f8000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_0
`define I3CCSR_DCT_DCT_MEMORY_0                                                                     (32'h0)
`define I3CCSR_DCT_DCT_MEMORY_0_PID_LO_LOW                                                          (32)
`define I3CCSR_DCT_DCT_MEMORY_0_PID_LO_MASK                                                         (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_0_DCR_LOW                                                             (64)
`define I3CCSR_DCT_DCT_MEMORY_0_DCR_MASK                                                            (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_0_BCR_LOW                                                             (72)
`define I3CCSR_DCT_DCT_MEMORY_0_BCR_MASK                                                            (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_0_DYNAMIC_ADDRESS_LOW                                                 (96)
`define I3CCSR_DCT_DCT_MEMORY_0_DYNAMIC_ADDRESS_MASK                                                (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_1
`define I3CCSR_DCT_DCT_MEMORY_1                                                                     (32'h10)
`define I3CCSR_DCT_DCT_MEMORY_1_PID_LO_LOW                                                          (32)
`define I3CCSR_DCT_DCT_MEMORY_1_PID_LO_MASK                                                         (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_1_DCR_LOW                                                             (64)
`define I3CCSR_DCT_DCT_MEMORY_1_DCR_MASK                                                            (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_1_BCR_LOW                                                             (72)
`define I3CCSR_DCT_DCT_MEMORY_1_BCR_MASK                                                            (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_1_DYNAMIC_ADDRESS_LOW                                                 (96)
`define I3CCSR_DCT_DCT_MEMORY_1_DYNAMIC_ADDRESS_MASK                                                (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_2
`define I3CCSR_DCT_DCT_MEMORY_2                                                                     (32'h20)
`define I3CCSR_DCT_DCT_MEMORY_2_PID_LO_LOW                                                          (32)
`define I3CCSR_DCT_DCT_MEMORY_2_PID_LO_MASK                                                         (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_2_DCR_LOW                                                             (64)
`define I3CCSR_DCT_DCT_MEMORY_2_DCR_MASK                                                            (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_2_BCR_LOW                                                             (72)
`define I3CCSR_DCT_DCT_MEMORY_2_BCR_MASK                                                            (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_2_DYNAMIC_ADDRESS_LOW                                                 (96)
`define I3CCSR_DCT_DCT_MEMORY_2_DYNAMIC_ADDRESS_MASK                                                (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_3
`define I3CCSR_DCT_DCT_MEMORY_3                                                                     (32'h30)
`define I3CCSR_DCT_DCT_MEMORY_3_PID_LO_LOW                                                          (32)
`define I3CCSR_DCT_DCT_MEMORY_3_PID_LO_MASK                                                         (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_3_DCR_LOW                                                             (64)
`define I3CCSR_DCT_DCT_MEMORY_3_DCR_MASK                                                            (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_3_BCR_LOW                                                             (72)
`define I3CCSR_DCT_DCT_MEMORY_3_BCR_MASK                                                            (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_3_DYNAMIC_ADDRESS_LOW                                                 (96)
`define I3CCSR_DCT_DCT_MEMORY_3_DYNAMIC_ADDRESS_MASK                                                (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_4
`define I3CCSR_DCT_DCT_MEMORY_4                                                                     (32'h40)
`define I3CCSR_DCT_DCT_MEMORY_4_PID_LO_LOW                                                          (32)
`define I3CCSR_DCT_DCT_MEMORY_4_PID_LO_MASK                                                         (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_4_DCR_LOW                                                             (64)
`define I3CCSR_DCT_DCT_MEMORY_4_DCR_MASK                                                            (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_4_BCR_LOW                                                             (72)
`define I3CCSR_DCT_DCT_MEMORY_4_BCR_MASK                                                            (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_4_DYNAMIC_ADDRESS_LOW                                                 (96)
`define I3CCSR_DCT_DCT_MEMORY_4_DYNAMIC_ADDRESS_MASK                                                (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_5
`define I3CCSR_DCT_DCT_MEMORY_5                                                                     (32'h50)
`define I3CCSR_DCT_DCT_MEMORY_5_PID_LO_LOW                                                          (32)
`define I3CCSR_DCT_DCT_MEMORY_5_PID_LO_MASK                                                         (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_5_DCR_LOW                                                             (64)
`define I3CCSR_DCT_DCT_MEMORY_5_DCR_MASK                                                            (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_5_BCR_LOW                                                             (72)
`define I3CCSR_DCT_DCT_MEMORY_5_BCR_MASK                                                            (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_5_DYNAMIC_ADDRESS_LOW                                                 (96)
`define I3CCSR_DCT_DCT_MEMORY_5_DYNAMIC_ADDRESS_MASK                                                (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_6
`define I3CCSR_DCT_DCT_MEMORY_6                                                                     (32'h60)
`define I3CCSR_DCT_DCT_MEMORY_6_PID_LO_LOW                                                          (32)
`define I3CCSR_DCT_DCT_MEMORY_6_PID_LO_MASK                                                         (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_6_DCR_LOW                                                             (64)
`define I3CCSR_DCT_DCT_MEMORY_6_DCR_MASK                                                            (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_6_BCR_LOW                                                             (72)
`define I3CCSR_DCT_DCT_MEMORY_6_BCR_MASK                                                            (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_6_DYNAMIC_ADDRESS_LOW                                                 (96)
`define I3CCSR_DCT_DCT_MEMORY_6_DYNAMIC_ADDRESS_MASK                                                (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_7
`define I3CCSR_DCT_DCT_MEMORY_7                                                                     (32'h70)
`define I3CCSR_DCT_DCT_MEMORY_7_PID_LO_LOW                                                          (32)
`define I3CCSR_DCT_DCT_MEMORY_7_PID_LO_MASK                                                         (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_7_DCR_LOW                                                             (64)
`define I3CCSR_DCT_DCT_MEMORY_7_DCR_MASK                                                            (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_7_BCR_LOW                                                             (72)
`define I3CCSR_DCT_DCT_MEMORY_7_BCR_MASK                                                            (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_7_DYNAMIC_ADDRESS_LOW                                                 (96)
`define I3CCSR_DCT_DCT_MEMORY_7_DYNAMIC_ADDRESS_MASK                                                (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_8
`define I3CCSR_DCT_DCT_MEMORY_8                                                                     (32'h80)
`define I3CCSR_DCT_DCT_MEMORY_8_PID_LO_LOW                                                          (32)
`define I3CCSR_DCT_DCT_MEMORY_8_PID_LO_MASK                                                         (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_8_DCR_LOW                                                             (64)
`define I3CCSR_DCT_DCT_MEMORY_8_DCR_MASK                                                            (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_8_BCR_LOW                                                             (72)
`define I3CCSR_DCT_DCT_MEMORY_8_BCR_MASK                                                            (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_8_DYNAMIC_ADDRESS_LOW                                                 (96)
`define I3CCSR_DCT_DCT_MEMORY_8_DYNAMIC_ADDRESS_MASK                                                (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_9
`define I3CCSR_DCT_DCT_MEMORY_9                                                                     (32'h90)
`define I3CCSR_DCT_DCT_MEMORY_9_PID_LO_LOW                                                          (32)
`define I3CCSR_DCT_DCT_MEMORY_9_PID_LO_MASK                                                         (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_9_DCR_LOW                                                             (64)
`define I3CCSR_DCT_DCT_MEMORY_9_DCR_MASK                                                            (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_9_BCR_LOW                                                             (72)
`define I3CCSR_DCT_DCT_MEMORY_9_BCR_MASK                                                            (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_9_DYNAMIC_ADDRESS_LOW                                                 (96)
`define I3CCSR_DCT_DCT_MEMORY_9_DYNAMIC_ADDRESS_MASK                                                (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_10
`define I3CCSR_DCT_DCT_MEMORY_10                                                                    (32'ha0)
`define I3CCSR_DCT_DCT_MEMORY_10_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_10_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_10_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_10_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_10_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_10_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_10_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_10_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_11
`define I3CCSR_DCT_DCT_MEMORY_11                                                                    (32'hb0)
`define I3CCSR_DCT_DCT_MEMORY_11_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_11_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_11_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_11_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_11_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_11_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_11_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_11_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_12
`define I3CCSR_DCT_DCT_MEMORY_12                                                                    (32'hc0)
`define I3CCSR_DCT_DCT_MEMORY_12_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_12_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_12_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_12_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_12_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_12_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_12_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_12_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_13
`define I3CCSR_DCT_DCT_MEMORY_13                                                                    (32'hd0)
`define I3CCSR_DCT_DCT_MEMORY_13_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_13_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_13_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_13_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_13_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_13_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_13_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_13_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_14
`define I3CCSR_DCT_DCT_MEMORY_14                                                                    (32'he0)
`define I3CCSR_DCT_DCT_MEMORY_14_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_14_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_14_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_14_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_14_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_14_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_14_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_14_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_15
`define I3CCSR_DCT_DCT_MEMORY_15                                                                    (32'hf0)
`define I3CCSR_DCT_DCT_MEMORY_15_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_15_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_15_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_15_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_15_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_15_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_15_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_15_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_16
`define I3CCSR_DCT_DCT_MEMORY_16                                                                    (32'h100)
`define I3CCSR_DCT_DCT_MEMORY_16_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_16_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_16_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_16_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_16_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_16_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_16_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_16_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_17
`define I3CCSR_DCT_DCT_MEMORY_17                                                                    (32'h110)
`define I3CCSR_DCT_DCT_MEMORY_17_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_17_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_17_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_17_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_17_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_17_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_17_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_17_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_18
`define I3CCSR_DCT_DCT_MEMORY_18                                                                    (32'h120)
`define I3CCSR_DCT_DCT_MEMORY_18_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_18_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_18_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_18_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_18_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_18_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_18_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_18_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_19
`define I3CCSR_DCT_DCT_MEMORY_19                                                                    (32'h130)
`define I3CCSR_DCT_DCT_MEMORY_19_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_19_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_19_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_19_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_19_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_19_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_19_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_19_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_20
`define I3CCSR_DCT_DCT_MEMORY_20                                                                    (32'h140)
`define I3CCSR_DCT_DCT_MEMORY_20_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_20_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_20_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_20_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_20_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_20_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_20_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_20_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_21
`define I3CCSR_DCT_DCT_MEMORY_21                                                                    (32'h150)
`define I3CCSR_DCT_DCT_MEMORY_21_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_21_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_21_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_21_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_21_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_21_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_21_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_21_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_22
`define I3CCSR_DCT_DCT_MEMORY_22                                                                    (32'h160)
`define I3CCSR_DCT_DCT_MEMORY_22_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_22_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_22_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_22_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_22_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_22_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_22_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_22_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_23
`define I3CCSR_DCT_DCT_MEMORY_23                                                                    (32'h170)
`define I3CCSR_DCT_DCT_MEMORY_23_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_23_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_23_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_23_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_23_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_23_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_23_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_23_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_24
`define I3CCSR_DCT_DCT_MEMORY_24                                                                    (32'h180)
`define I3CCSR_DCT_DCT_MEMORY_24_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_24_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_24_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_24_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_24_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_24_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_24_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_24_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_25
`define I3CCSR_DCT_DCT_MEMORY_25                                                                    (32'h190)
`define I3CCSR_DCT_DCT_MEMORY_25_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_25_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_25_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_25_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_25_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_25_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_25_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_25_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_26
`define I3CCSR_DCT_DCT_MEMORY_26                                                                    (32'h1a0)
`define I3CCSR_DCT_DCT_MEMORY_26_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_26_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_26_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_26_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_26_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_26_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_26_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_26_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_27
`define I3CCSR_DCT_DCT_MEMORY_27                                                                    (32'h1b0)
`define I3CCSR_DCT_DCT_MEMORY_27_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_27_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_27_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_27_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_27_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_27_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_27_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_27_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_28
`define I3CCSR_DCT_DCT_MEMORY_28                                                                    (32'h1c0)
`define I3CCSR_DCT_DCT_MEMORY_28_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_28_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_28_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_28_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_28_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_28_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_28_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_28_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_29
`define I3CCSR_DCT_DCT_MEMORY_29                                                                    (32'h1d0)
`define I3CCSR_DCT_DCT_MEMORY_29_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_29_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_29_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_29_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_29_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_29_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_29_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_29_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_30
`define I3CCSR_DCT_DCT_MEMORY_30                                                                    (32'h1e0)
`define I3CCSR_DCT_DCT_MEMORY_30_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_30_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_30_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_30_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_30_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_30_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_30_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_30_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_31
`define I3CCSR_DCT_DCT_MEMORY_31                                                                    (32'h1f0)
`define I3CCSR_DCT_DCT_MEMORY_31_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_31_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_31_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_31_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_31_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_31_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_31_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_31_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_32
`define I3CCSR_DCT_DCT_MEMORY_32                                                                    (32'h200)
`define I3CCSR_DCT_DCT_MEMORY_32_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_32_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_32_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_32_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_32_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_32_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_32_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_32_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_33
`define I3CCSR_DCT_DCT_MEMORY_33                                                                    (32'h210)
`define I3CCSR_DCT_DCT_MEMORY_33_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_33_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_33_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_33_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_33_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_33_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_33_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_33_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_34
`define I3CCSR_DCT_DCT_MEMORY_34                                                                    (32'h220)
`define I3CCSR_DCT_DCT_MEMORY_34_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_34_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_34_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_34_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_34_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_34_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_34_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_34_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_35
`define I3CCSR_DCT_DCT_MEMORY_35                                                                    (32'h230)
`define I3CCSR_DCT_DCT_MEMORY_35_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_35_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_35_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_35_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_35_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_35_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_35_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_35_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_36
`define I3CCSR_DCT_DCT_MEMORY_36                                                                    (32'h240)
`define I3CCSR_DCT_DCT_MEMORY_36_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_36_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_36_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_36_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_36_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_36_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_36_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_36_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_37
`define I3CCSR_DCT_DCT_MEMORY_37                                                                    (32'h250)
`define I3CCSR_DCT_DCT_MEMORY_37_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_37_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_37_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_37_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_37_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_37_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_37_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_37_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_38
`define I3CCSR_DCT_DCT_MEMORY_38                                                                    (32'h260)
`define I3CCSR_DCT_DCT_MEMORY_38_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_38_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_38_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_38_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_38_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_38_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_38_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_38_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_39
`define I3CCSR_DCT_DCT_MEMORY_39                                                                    (32'h270)
`define I3CCSR_DCT_DCT_MEMORY_39_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_39_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_39_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_39_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_39_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_39_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_39_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_39_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_40
`define I3CCSR_DCT_DCT_MEMORY_40                                                                    (32'h280)
`define I3CCSR_DCT_DCT_MEMORY_40_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_40_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_40_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_40_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_40_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_40_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_40_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_40_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_41
`define I3CCSR_DCT_DCT_MEMORY_41                                                                    (32'h290)
`define I3CCSR_DCT_DCT_MEMORY_41_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_41_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_41_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_41_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_41_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_41_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_41_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_41_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_42
`define I3CCSR_DCT_DCT_MEMORY_42                                                                    (32'h2a0)
`define I3CCSR_DCT_DCT_MEMORY_42_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_42_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_42_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_42_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_42_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_42_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_42_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_42_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_43
`define I3CCSR_DCT_DCT_MEMORY_43                                                                    (32'h2b0)
`define I3CCSR_DCT_DCT_MEMORY_43_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_43_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_43_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_43_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_43_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_43_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_43_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_43_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_44
`define I3CCSR_DCT_DCT_MEMORY_44                                                                    (32'h2c0)
`define I3CCSR_DCT_DCT_MEMORY_44_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_44_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_44_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_44_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_44_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_44_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_44_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_44_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_45
`define I3CCSR_DCT_DCT_MEMORY_45                                                                    (32'h2d0)
`define I3CCSR_DCT_DCT_MEMORY_45_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_45_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_45_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_45_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_45_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_45_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_45_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_45_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_46
`define I3CCSR_DCT_DCT_MEMORY_46                                                                    (32'h2e0)
`define I3CCSR_DCT_DCT_MEMORY_46_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_46_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_46_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_46_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_46_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_46_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_46_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_46_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_47
`define I3CCSR_DCT_DCT_MEMORY_47                                                                    (32'h2f0)
`define I3CCSR_DCT_DCT_MEMORY_47_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_47_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_47_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_47_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_47_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_47_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_47_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_47_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_48
`define I3CCSR_DCT_DCT_MEMORY_48                                                                    (32'h300)
`define I3CCSR_DCT_DCT_MEMORY_48_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_48_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_48_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_48_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_48_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_48_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_48_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_48_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_49
`define I3CCSR_DCT_DCT_MEMORY_49                                                                    (32'h310)
`define I3CCSR_DCT_DCT_MEMORY_49_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_49_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_49_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_49_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_49_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_49_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_49_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_49_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_50
`define I3CCSR_DCT_DCT_MEMORY_50                                                                    (32'h320)
`define I3CCSR_DCT_DCT_MEMORY_50_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_50_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_50_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_50_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_50_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_50_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_50_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_50_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_51
`define I3CCSR_DCT_DCT_MEMORY_51                                                                    (32'h330)
`define I3CCSR_DCT_DCT_MEMORY_51_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_51_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_51_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_51_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_51_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_51_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_51_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_51_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_52
`define I3CCSR_DCT_DCT_MEMORY_52                                                                    (32'h340)
`define I3CCSR_DCT_DCT_MEMORY_52_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_52_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_52_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_52_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_52_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_52_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_52_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_52_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_53
`define I3CCSR_DCT_DCT_MEMORY_53                                                                    (32'h350)
`define I3CCSR_DCT_DCT_MEMORY_53_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_53_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_53_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_53_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_53_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_53_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_53_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_53_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_54
`define I3CCSR_DCT_DCT_MEMORY_54                                                                    (32'h360)
`define I3CCSR_DCT_DCT_MEMORY_54_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_54_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_54_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_54_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_54_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_54_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_54_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_54_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_55
`define I3CCSR_DCT_DCT_MEMORY_55                                                                    (32'h370)
`define I3CCSR_DCT_DCT_MEMORY_55_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_55_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_55_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_55_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_55_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_55_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_55_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_55_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_56
`define I3CCSR_DCT_DCT_MEMORY_56                                                                    (32'h380)
`define I3CCSR_DCT_DCT_MEMORY_56_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_56_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_56_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_56_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_56_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_56_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_56_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_56_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_57
`define I3CCSR_DCT_DCT_MEMORY_57                                                                    (32'h390)
`define I3CCSR_DCT_DCT_MEMORY_57_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_57_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_57_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_57_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_57_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_57_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_57_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_57_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_58
`define I3CCSR_DCT_DCT_MEMORY_58                                                                    (32'h3a0)
`define I3CCSR_DCT_DCT_MEMORY_58_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_58_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_58_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_58_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_58_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_58_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_58_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_58_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_59
`define I3CCSR_DCT_DCT_MEMORY_59                                                                    (32'h3b0)
`define I3CCSR_DCT_DCT_MEMORY_59_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_59_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_59_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_59_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_59_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_59_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_59_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_59_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_60
`define I3CCSR_DCT_DCT_MEMORY_60                                                                    (32'h3c0)
`define I3CCSR_DCT_DCT_MEMORY_60_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_60_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_60_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_60_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_60_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_60_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_60_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_60_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_61
`define I3CCSR_DCT_DCT_MEMORY_61                                                                    (32'h3d0)
`define I3CCSR_DCT_DCT_MEMORY_61_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_61_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_61_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_61_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_61_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_61_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_61_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_61_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_62
`define I3CCSR_DCT_DCT_MEMORY_62                                                                    (32'h3e0)
`define I3CCSR_DCT_DCT_MEMORY_62_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_62_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_62_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_62_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_62_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_62_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_62_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_62_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_63
`define I3CCSR_DCT_DCT_MEMORY_63                                                                    (32'h3f0)
`define I3CCSR_DCT_DCT_MEMORY_63_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_63_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_63_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_63_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_63_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_63_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_63_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_63_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_64
`define I3CCSR_DCT_DCT_MEMORY_64                                                                    (32'h400)
`define I3CCSR_DCT_DCT_MEMORY_64_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_64_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_64_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_64_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_64_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_64_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_64_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_64_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_65
`define I3CCSR_DCT_DCT_MEMORY_65                                                                    (32'h410)
`define I3CCSR_DCT_DCT_MEMORY_65_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_65_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_65_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_65_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_65_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_65_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_65_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_65_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_66
`define I3CCSR_DCT_DCT_MEMORY_66                                                                    (32'h420)
`define I3CCSR_DCT_DCT_MEMORY_66_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_66_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_66_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_66_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_66_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_66_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_66_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_66_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_67
`define I3CCSR_DCT_DCT_MEMORY_67                                                                    (32'h430)
`define I3CCSR_DCT_DCT_MEMORY_67_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_67_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_67_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_67_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_67_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_67_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_67_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_67_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_68
`define I3CCSR_DCT_DCT_MEMORY_68                                                                    (32'h440)
`define I3CCSR_DCT_DCT_MEMORY_68_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_68_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_68_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_68_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_68_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_68_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_68_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_68_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_69
`define I3CCSR_DCT_DCT_MEMORY_69                                                                    (32'h450)
`define I3CCSR_DCT_DCT_MEMORY_69_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_69_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_69_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_69_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_69_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_69_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_69_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_69_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_70
`define I3CCSR_DCT_DCT_MEMORY_70                                                                    (32'h460)
`define I3CCSR_DCT_DCT_MEMORY_70_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_70_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_70_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_70_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_70_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_70_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_70_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_70_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_71
`define I3CCSR_DCT_DCT_MEMORY_71                                                                    (32'h470)
`define I3CCSR_DCT_DCT_MEMORY_71_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_71_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_71_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_71_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_71_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_71_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_71_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_71_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_72
`define I3CCSR_DCT_DCT_MEMORY_72                                                                    (32'h480)
`define I3CCSR_DCT_DCT_MEMORY_72_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_72_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_72_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_72_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_72_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_72_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_72_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_72_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_73
`define I3CCSR_DCT_DCT_MEMORY_73                                                                    (32'h490)
`define I3CCSR_DCT_DCT_MEMORY_73_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_73_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_73_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_73_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_73_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_73_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_73_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_73_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_74
`define I3CCSR_DCT_DCT_MEMORY_74                                                                    (32'h4a0)
`define I3CCSR_DCT_DCT_MEMORY_74_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_74_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_74_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_74_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_74_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_74_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_74_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_74_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_75
`define I3CCSR_DCT_DCT_MEMORY_75                                                                    (32'h4b0)
`define I3CCSR_DCT_DCT_MEMORY_75_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_75_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_75_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_75_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_75_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_75_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_75_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_75_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_76
`define I3CCSR_DCT_DCT_MEMORY_76                                                                    (32'h4c0)
`define I3CCSR_DCT_DCT_MEMORY_76_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_76_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_76_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_76_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_76_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_76_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_76_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_76_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_77
`define I3CCSR_DCT_DCT_MEMORY_77                                                                    (32'h4d0)
`define I3CCSR_DCT_DCT_MEMORY_77_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_77_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_77_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_77_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_77_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_77_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_77_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_77_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_78
`define I3CCSR_DCT_DCT_MEMORY_78                                                                    (32'h4e0)
`define I3CCSR_DCT_DCT_MEMORY_78_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_78_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_78_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_78_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_78_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_78_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_78_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_78_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_79
`define I3CCSR_DCT_DCT_MEMORY_79                                                                    (32'h4f0)
`define I3CCSR_DCT_DCT_MEMORY_79_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_79_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_79_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_79_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_79_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_79_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_79_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_79_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_80
`define I3CCSR_DCT_DCT_MEMORY_80                                                                    (32'h500)
`define I3CCSR_DCT_DCT_MEMORY_80_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_80_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_80_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_80_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_80_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_80_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_80_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_80_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_81
`define I3CCSR_DCT_DCT_MEMORY_81                                                                    (32'h510)
`define I3CCSR_DCT_DCT_MEMORY_81_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_81_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_81_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_81_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_81_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_81_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_81_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_81_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_82
`define I3CCSR_DCT_DCT_MEMORY_82                                                                    (32'h520)
`define I3CCSR_DCT_DCT_MEMORY_82_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_82_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_82_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_82_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_82_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_82_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_82_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_82_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_83
`define I3CCSR_DCT_DCT_MEMORY_83                                                                    (32'h530)
`define I3CCSR_DCT_DCT_MEMORY_83_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_83_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_83_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_83_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_83_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_83_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_83_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_83_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_84
`define I3CCSR_DCT_DCT_MEMORY_84                                                                    (32'h540)
`define I3CCSR_DCT_DCT_MEMORY_84_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_84_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_84_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_84_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_84_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_84_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_84_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_84_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_85
`define I3CCSR_DCT_DCT_MEMORY_85                                                                    (32'h550)
`define I3CCSR_DCT_DCT_MEMORY_85_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_85_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_85_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_85_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_85_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_85_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_85_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_85_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_86
`define I3CCSR_DCT_DCT_MEMORY_86                                                                    (32'h560)
`define I3CCSR_DCT_DCT_MEMORY_86_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_86_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_86_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_86_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_86_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_86_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_86_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_86_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_87
`define I3CCSR_DCT_DCT_MEMORY_87                                                                    (32'h570)
`define I3CCSR_DCT_DCT_MEMORY_87_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_87_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_87_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_87_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_87_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_87_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_87_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_87_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_88
`define I3CCSR_DCT_DCT_MEMORY_88                                                                    (32'h580)
`define I3CCSR_DCT_DCT_MEMORY_88_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_88_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_88_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_88_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_88_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_88_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_88_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_88_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_89
`define I3CCSR_DCT_DCT_MEMORY_89                                                                    (32'h590)
`define I3CCSR_DCT_DCT_MEMORY_89_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_89_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_89_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_89_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_89_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_89_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_89_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_89_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_90
`define I3CCSR_DCT_DCT_MEMORY_90                                                                    (32'h5a0)
`define I3CCSR_DCT_DCT_MEMORY_90_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_90_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_90_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_90_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_90_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_90_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_90_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_90_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_91
`define I3CCSR_DCT_DCT_MEMORY_91                                                                    (32'h5b0)
`define I3CCSR_DCT_DCT_MEMORY_91_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_91_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_91_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_91_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_91_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_91_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_91_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_91_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_92
`define I3CCSR_DCT_DCT_MEMORY_92                                                                    (32'h5c0)
`define I3CCSR_DCT_DCT_MEMORY_92_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_92_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_92_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_92_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_92_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_92_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_92_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_92_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_93
`define I3CCSR_DCT_DCT_MEMORY_93                                                                    (32'h5d0)
`define I3CCSR_DCT_DCT_MEMORY_93_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_93_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_93_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_93_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_93_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_93_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_93_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_93_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_94
`define I3CCSR_DCT_DCT_MEMORY_94                                                                    (32'h5e0)
`define I3CCSR_DCT_DCT_MEMORY_94_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_94_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_94_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_94_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_94_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_94_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_94_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_94_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_95
`define I3CCSR_DCT_DCT_MEMORY_95                                                                    (32'h5f0)
`define I3CCSR_DCT_DCT_MEMORY_95_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_95_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_95_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_95_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_95_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_95_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_95_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_95_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_96
`define I3CCSR_DCT_DCT_MEMORY_96                                                                    (32'h600)
`define I3CCSR_DCT_DCT_MEMORY_96_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_96_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_96_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_96_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_96_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_96_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_96_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_96_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_97
`define I3CCSR_DCT_DCT_MEMORY_97                                                                    (32'h610)
`define I3CCSR_DCT_DCT_MEMORY_97_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_97_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_97_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_97_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_97_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_97_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_97_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_97_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_98
`define I3CCSR_DCT_DCT_MEMORY_98                                                                    (32'h620)
`define I3CCSR_DCT_DCT_MEMORY_98_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_98_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_98_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_98_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_98_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_98_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_98_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_98_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_99
`define I3CCSR_DCT_DCT_MEMORY_99                                                                    (32'h630)
`define I3CCSR_DCT_DCT_MEMORY_99_PID_LO_LOW                                                         (32)
`define I3CCSR_DCT_DCT_MEMORY_99_PID_LO_MASK                                                        (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_99_DCR_LOW                                                            (64)
`define I3CCSR_DCT_DCT_MEMORY_99_DCR_MASK                                                           (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_99_BCR_LOW                                                            (72)
`define I3CCSR_DCT_DCT_MEMORY_99_BCR_MASK                                                           (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_99_DYNAMIC_ADDRESS_LOW                                                (96)
`define I3CCSR_DCT_DCT_MEMORY_99_DYNAMIC_ADDRESS_MASK                                               (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_100
`define I3CCSR_DCT_DCT_MEMORY_100                                                                   (32'h640)
`define I3CCSR_DCT_DCT_MEMORY_100_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_100_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_100_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_100_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_100_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_100_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_100_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_100_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_101
`define I3CCSR_DCT_DCT_MEMORY_101                                                                   (32'h650)
`define I3CCSR_DCT_DCT_MEMORY_101_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_101_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_101_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_101_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_101_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_101_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_101_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_101_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_102
`define I3CCSR_DCT_DCT_MEMORY_102                                                                   (32'h660)
`define I3CCSR_DCT_DCT_MEMORY_102_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_102_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_102_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_102_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_102_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_102_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_102_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_102_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_103
`define I3CCSR_DCT_DCT_MEMORY_103                                                                   (32'h670)
`define I3CCSR_DCT_DCT_MEMORY_103_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_103_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_103_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_103_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_103_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_103_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_103_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_103_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_104
`define I3CCSR_DCT_DCT_MEMORY_104                                                                   (32'h680)
`define I3CCSR_DCT_DCT_MEMORY_104_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_104_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_104_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_104_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_104_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_104_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_104_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_104_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_105
`define I3CCSR_DCT_DCT_MEMORY_105                                                                   (32'h690)
`define I3CCSR_DCT_DCT_MEMORY_105_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_105_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_105_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_105_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_105_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_105_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_105_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_105_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_106
`define I3CCSR_DCT_DCT_MEMORY_106                                                                   (32'h6a0)
`define I3CCSR_DCT_DCT_MEMORY_106_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_106_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_106_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_106_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_106_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_106_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_106_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_106_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_107
`define I3CCSR_DCT_DCT_MEMORY_107                                                                   (32'h6b0)
`define I3CCSR_DCT_DCT_MEMORY_107_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_107_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_107_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_107_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_107_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_107_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_107_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_107_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_108
`define I3CCSR_DCT_DCT_MEMORY_108                                                                   (32'h6c0)
`define I3CCSR_DCT_DCT_MEMORY_108_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_108_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_108_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_108_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_108_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_108_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_108_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_108_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_109
`define I3CCSR_DCT_DCT_MEMORY_109                                                                   (32'h6d0)
`define I3CCSR_DCT_DCT_MEMORY_109_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_109_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_109_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_109_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_109_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_109_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_109_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_109_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_110
`define I3CCSR_DCT_DCT_MEMORY_110                                                                   (32'h6e0)
`define I3CCSR_DCT_DCT_MEMORY_110_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_110_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_110_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_110_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_110_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_110_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_110_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_110_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_111
`define I3CCSR_DCT_DCT_MEMORY_111                                                                   (32'h6f0)
`define I3CCSR_DCT_DCT_MEMORY_111_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_111_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_111_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_111_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_111_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_111_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_111_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_111_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_112
`define I3CCSR_DCT_DCT_MEMORY_112                                                                   (32'h700)
`define I3CCSR_DCT_DCT_MEMORY_112_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_112_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_112_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_112_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_112_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_112_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_112_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_112_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_113
`define I3CCSR_DCT_DCT_MEMORY_113                                                                   (32'h710)
`define I3CCSR_DCT_DCT_MEMORY_113_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_113_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_113_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_113_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_113_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_113_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_113_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_113_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_114
`define I3CCSR_DCT_DCT_MEMORY_114                                                                   (32'h720)
`define I3CCSR_DCT_DCT_MEMORY_114_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_114_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_114_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_114_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_114_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_114_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_114_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_114_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_115
`define I3CCSR_DCT_DCT_MEMORY_115                                                                   (32'h730)
`define I3CCSR_DCT_DCT_MEMORY_115_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_115_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_115_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_115_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_115_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_115_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_115_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_115_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_116
`define I3CCSR_DCT_DCT_MEMORY_116                                                                   (32'h740)
`define I3CCSR_DCT_DCT_MEMORY_116_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_116_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_116_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_116_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_116_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_116_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_116_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_116_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_117
`define I3CCSR_DCT_DCT_MEMORY_117                                                                   (32'h750)
`define I3CCSR_DCT_DCT_MEMORY_117_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_117_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_117_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_117_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_117_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_117_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_117_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_117_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_118
`define I3CCSR_DCT_DCT_MEMORY_118                                                                   (32'h760)
`define I3CCSR_DCT_DCT_MEMORY_118_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_118_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_118_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_118_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_118_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_118_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_118_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_118_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_119
`define I3CCSR_DCT_DCT_MEMORY_119                                                                   (32'h770)
`define I3CCSR_DCT_DCT_MEMORY_119_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_119_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_119_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_119_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_119_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_119_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_119_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_119_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_120
`define I3CCSR_DCT_DCT_MEMORY_120                                                                   (32'h780)
`define I3CCSR_DCT_DCT_MEMORY_120_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_120_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_120_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_120_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_120_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_120_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_120_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_120_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_121
`define I3CCSR_DCT_DCT_MEMORY_121                                                                   (32'h790)
`define I3CCSR_DCT_DCT_MEMORY_121_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_121_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_121_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_121_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_121_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_121_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_121_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_121_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_122
`define I3CCSR_DCT_DCT_MEMORY_122                                                                   (32'h7a0)
`define I3CCSR_DCT_DCT_MEMORY_122_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_122_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_122_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_122_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_122_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_122_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_122_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_122_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_123
`define I3CCSR_DCT_DCT_MEMORY_123                                                                   (32'h7b0)
`define I3CCSR_DCT_DCT_MEMORY_123_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_123_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_123_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_123_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_123_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_123_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_123_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_123_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_124
`define I3CCSR_DCT_DCT_MEMORY_124                                                                   (32'h7c0)
`define I3CCSR_DCT_DCT_MEMORY_124_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_124_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_124_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_124_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_124_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_124_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_124_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_124_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_125
`define I3CCSR_DCT_DCT_MEMORY_125                                                                   (32'h7d0)
`define I3CCSR_DCT_DCT_MEMORY_125_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_125_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_125_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_125_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_125_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_125_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_125_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_125_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_126
`define I3CCSR_DCT_DCT_MEMORY_126                                                                   (32'h7e0)
`define I3CCSR_DCT_DCT_MEMORY_126_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_126_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_126_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_126_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_126_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_126_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_126_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_126_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
`ifndef I3CCSR_DCT_DCT_MEMORY_127
`define I3CCSR_DCT_DCT_MEMORY_127                                                                   (32'h7f0)
`define I3CCSR_DCT_DCT_MEMORY_127_PID_LO_LOW                                                        (32)
`define I3CCSR_DCT_DCT_MEMORY_127_PID_LO_MASK                                                       (32'hffff00000000)
`define I3CCSR_DCT_DCT_MEMORY_127_DCR_LOW                                                           (64)
`define I3CCSR_DCT_DCT_MEMORY_127_DCR_MASK                                                          (32'hff0000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_127_BCR_LOW                                                           (72)
`define I3CCSR_DCT_DCT_MEMORY_127_BCR_MASK                                                          (32'hff000000000000000000)
`define I3CCSR_DCT_DCT_MEMORY_127_DYNAMIC_ADDRESS_LOW                                               (96)
`define I3CCSR_DCT_DCT_MEMORY_127_DYNAMIC_ADDRESS_MASK                                              (32'hff000000000000000000000000)
`endif
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
`define MCI_REG_HW_CONFIG0_MCU_MBOX1_SRAM_SIZE_LOW                                                  (0)
`define MCI_REG_HW_CONFIG0_MCU_MBOX1_SRAM_SIZE_MASK                                                 (32'hfff)
`define MCI_REG_HW_CONFIG0_MCU_MBOX0_SRAM_SIZE_LOW                                                  (12)
`define MCI_REG_HW_CONFIG0_MCU_MBOX0_SRAM_SIZE_MASK                                                 (32'hfff000)
`endif
`ifndef MCI_REG_HW_CONFIG1
`define MCI_REG_HW_CONFIG1                                                                          (32'h1c)
`define MCI_REG_HW_CONFIG1_MIN_MCU_RST_COUNTER_WIDTH_LOW                                            (0)
`define MCI_REG_HW_CONFIG1_MIN_MCU_RST_COUNTER_WIDTH_MASK                                           (32'h1f)
`define MCI_REG_HW_CONFIG1_MCU_SRAM_SIZE_LOW                                                        (5)
`define MCI_REG_HW_CONFIG1_MCU_SRAM_SIZE_MASK                                                       (32'h1ffe0)
`endif
`ifndef MCI_REG_MCU_IFU_AXI_USER
`define MCI_REG_MCU_IFU_AXI_USER                                                                    (32'h20)
`endif
`ifndef MCI_REG_MCU_LSU_AXI_USER
`define MCI_REG_MCU_LSU_AXI_USER                                                                    (32'h24)
`endif
`ifndef MCI_REG_MCU_SRAM_CONFIG_AXI_USER
`define MCI_REG_MCU_SRAM_CONFIG_AXI_USER                                                            (32'h28)
`endif
`ifndef MCI_REG_MCI_SOC_CONFIG_AXI_USER
`define MCI_REG_MCI_SOC_CONFIG_AXI_USER                                                             (32'h2c)
`endif
`ifndef MCI_REG_FW_FLOW_STATUS
`define MCI_REG_FW_FLOW_STATUS                                                                      (32'h30)
`endif
`ifndef MCI_REG_HW_FLOW_STATUS
`define MCI_REG_HW_FLOW_STATUS                                                                      (32'h34)
`define MCI_REG_HW_FLOW_STATUS_BOOT_FSM_LOW                                                         (0)
`define MCI_REG_HW_FLOW_STATUS_BOOT_FSM_MASK                                                        (32'hf)
`endif
`ifndef MCI_REG_RESET_REASON
`define MCI_REG_RESET_REASON                                                                        (32'h38)
`define MCI_REG_RESET_REASON_FW_HITLESS_UPD_RESET_LOW                                               (0)
`define MCI_REG_RESET_REASON_FW_HITLESS_UPD_RESET_MASK                                              (32'h1)
`define MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_LOW                                                  (1)
`define MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_MASK                                                 (32'h2)
`define MCI_REG_RESET_REASON_WARM_RESET_LOW                                                         (2)
`define MCI_REG_RESET_REASON_WARM_RESET_MASK                                                        (32'h4)
`endif
`ifndef MCI_REG_RESET_STATUS
`define MCI_REG_RESET_STATUS                                                                        (32'h3c)
`define MCI_REG_RESET_STATUS_CPTRA_RESET_STS_LOW                                                    (0)
`define MCI_REG_RESET_STATUS_CPTRA_RESET_STS_MASK                                                   (32'h1)
`define MCI_REG_RESET_STATUS_MCU_RESET_STS_LOW                                                      (1)
`define MCI_REG_RESET_STATUS_MCU_RESET_STS_MASK                                                     (32'h2)
`endif
`ifndef MCI_REG_SECURITY_STATE
`define MCI_REG_SECURITY_STATE                                                                      (32'h40)
`define MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_LOW                                                 (0)
`define MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_MASK                                                (32'h3)
`define MCI_REG_SECURITY_STATE_DEBUG_LOCKED_LOW                                                     (2)
`define MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK                                                    (32'h4)
`define MCI_REG_SECURITY_STATE_SCAN_MODE_LOW                                                        (3)
`define MCI_REG_SECURITY_STATE_SCAN_MODE_MASK                                                       (32'h8)
`endif
`ifndef MCI_REG_HW_ERROR_FATAL
`define MCI_REG_HW_ERROR_FATAL                                                                      (32'h50)
`define MCI_REG_HW_ERROR_FATAL_MCU_SRAM_ECC_UNC_LOW                                                 (0)
`define MCI_REG_HW_ERROR_FATAL_MCU_SRAM_ECC_UNC_MASK                                                (32'h1)
`define MCI_REG_HW_ERROR_FATAL_NMI_PIN_LOW                                                          (1)
`define MCI_REG_HW_ERROR_FATAL_NMI_PIN_MASK                                                         (32'h2)
`define MCI_REG_HW_ERROR_FATAL_MCU_SRAM_DMI_AXI_COLLISION_LOW                                       (2)
`define MCI_REG_HW_ERROR_FATAL_MCU_SRAM_DMI_AXI_COLLISION_MASK                                      (32'h4)
`endif
`ifndef MCI_REG_AGG_ERROR_FATAL
`define MCI_REG_AGG_ERROR_FATAL                                                                     (32'h54)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL0_LOW                                                (0)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL0_MASK                                               (32'h1)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL1_LOW                                                (1)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL1_MASK                                               (32'h2)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL2_LOW                                                (2)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL2_MASK                                               (32'h4)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL3_LOW                                                (3)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL3_MASK                                               (32'h8)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL4_LOW                                                (4)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL4_MASK                                               (32'h10)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL5_LOW                                                (5)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL5_MASK                                               (32'h20)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL6_LOW                                                (6)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL6_MASK                                               (32'h40)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL7_LOW                                                (7)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL7_MASK                                               (32'h80)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL8_LOW                                                (8)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL8_MASK                                               (32'h100)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL9_LOW                                                (9)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL9_MASK                                               (32'h200)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL10_LOW                                               (10)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL10_MASK                                              (32'h400)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL11_LOW                                               (11)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL11_MASK                                              (32'h800)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL12_LOW                                               (12)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL12_MASK                                              (32'h1000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL13_LOW                                               (13)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL13_MASK                                              (32'h2000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL14_LOW                                               (14)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL14_MASK                                              (32'h4000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL15_LOW                                               (15)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL15_MASK                                              (32'h8000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL16_LOW                                               (16)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL16_MASK                                              (32'h10000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL17_LOW                                               (17)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL17_MASK                                              (32'h20000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL18_LOW                                               (18)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL18_MASK                                              (32'h40000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL19_LOW                                               (19)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL19_MASK                                              (32'h80000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL20_LOW                                               (20)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL20_MASK                                              (32'h100000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL21_LOW                                               (21)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL21_MASK                                              (32'h200000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL22_LOW                                               (22)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL22_MASK                                              (32'h400000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL23_LOW                                               (23)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL23_MASK                                              (32'h800000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL24_LOW                                               (24)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL24_MASK                                              (32'h1000000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL25_LOW                                               (25)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL25_MASK                                              (32'h2000000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL26_LOW                                               (26)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL26_MASK                                              (32'h4000000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL27_LOW                                               (27)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL27_MASK                                              (32'h8000000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL28_LOW                                               (28)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL28_MASK                                              (32'h10000000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL29_LOW                                               (29)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL29_MASK                                              (32'h20000000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL30_LOW                                               (30)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL30_MASK                                              (32'h40000000)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL31_LOW                                               (31)
`define MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL31_MASK                                              (32'h80000000)
`endif
`ifndef MCI_REG_HW_ERROR_NON_FATAL
`define MCI_REG_HW_ERROR_NON_FATAL                                                                  (32'h58)
`define MCI_REG_HW_ERROR_NON_FATAL_MBOX0_ECC_UNC_LOW                                                (0)
`define MCI_REG_HW_ERROR_NON_FATAL_MBOX0_ECC_UNC_MASK                                               (32'h1)
`define MCI_REG_HW_ERROR_NON_FATAL_MBOX1_ECC_UNC_LOW                                                (1)
`define MCI_REG_HW_ERROR_NON_FATAL_MBOX1_ECC_UNC_MASK                                               (32'h2)
`endif
`ifndef MCI_REG_AGG_ERROR_NON_FATAL
`define MCI_REG_AGG_ERROR_NON_FATAL                                                                 (32'h5c)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL0_LOW                                        (0)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL0_MASK                                       (32'h1)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL1_LOW                                        (1)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL1_MASK                                       (32'h2)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL2_LOW                                        (2)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL2_MASK                                       (32'h4)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL3_LOW                                        (3)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL3_MASK                                       (32'h8)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL4_LOW                                        (4)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL4_MASK                                       (32'h10)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL5_LOW                                        (5)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL5_MASK                                       (32'h20)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL6_LOW                                        (6)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL6_MASK                                       (32'h40)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL7_LOW                                        (7)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL7_MASK                                       (32'h80)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL8_LOW                                        (8)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL8_MASK                                       (32'h100)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL9_LOW                                        (9)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL9_MASK                                       (32'h200)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL10_LOW                                       (10)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL10_MASK                                      (32'h400)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL11_LOW                                       (11)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL11_MASK                                      (32'h800)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL12_LOW                                       (12)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL12_MASK                                      (32'h1000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL13_LOW                                       (13)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL13_MASK                                      (32'h2000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL14_LOW                                       (14)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL14_MASK                                      (32'h4000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL15_LOW                                       (15)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL15_MASK                                      (32'h8000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL16_LOW                                       (16)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL16_MASK                                      (32'h10000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL17_LOW                                       (17)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL17_MASK                                      (32'h20000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL18_LOW                                       (18)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL18_MASK                                      (32'h40000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL19_LOW                                       (19)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL19_MASK                                      (32'h80000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL20_LOW                                       (20)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL20_MASK                                      (32'h100000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL21_LOW                                       (21)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL21_MASK                                      (32'h200000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL22_LOW                                       (22)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL22_MASK                                      (32'h400000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL23_LOW                                       (23)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL23_MASK                                      (32'h800000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL24_LOW                                       (24)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL24_MASK                                      (32'h1000000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL25_LOW                                       (25)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL25_MASK                                      (32'h2000000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL26_LOW                                       (26)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL26_MASK                                      (32'h4000000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL27_LOW                                       (27)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL27_MASK                                      (32'h8000000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL28_LOW                                       (28)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL28_MASK                                      (32'h10000000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL29_LOW                                       (29)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL29_MASK                                      (32'h20000000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL30_LOW                                       (30)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL30_MASK                                      (32'h40000000)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL31_LOW                                       (31)
`define MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL31_MASK                                      (32'h80000000)
`endif
`ifndef MCI_REG_FW_ERROR_FATAL
`define MCI_REG_FW_ERROR_FATAL                                                                      (32'h60)
`endif
`ifndef MCI_REG_FW_ERROR_NON_FATAL
`define MCI_REG_FW_ERROR_NON_FATAL                                                                  (32'h64)
`endif
`ifndef MCI_REG_HW_ERROR_ENC
`define MCI_REG_HW_ERROR_ENC                                                                        (32'h68)
`endif
`ifndef MCI_REG_FW_ERROR_ENC
`define MCI_REG_FW_ERROR_ENC                                                                        (32'h6c)
`endif
`ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_0
`define MCI_REG_FW_EXTENDED_ERROR_INFO_0                                                            (32'h70)
`endif
`ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_1
`define MCI_REG_FW_EXTENDED_ERROR_INFO_1                                                            (32'h74)
`endif
`ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_2
`define MCI_REG_FW_EXTENDED_ERROR_INFO_2                                                            (32'h78)
`endif
`ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_3
`define MCI_REG_FW_EXTENDED_ERROR_INFO_3                                                            (32'h7c)
`endif
`ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_4
`define MCI_REG_FW_EXTENDED_ERROR_INFO_4                                                            (32'h80)
`endif
`ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_5
`define MCI_REG_FW_EXTENDED_ERROR_INFO_5                                                            (32'h84)
`endif
`ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_6
`define MCI_REG_FW_EXTENDED_ERROR_INFO_6                                                            (32'h88)
`endif
`ifndef MCI_REG_FW_EXTENDED_ERROR_INFO_7
`define MCI_REG_FW_EXTENDED_ERROR_INFO_7                                                            (32'h8c)
`endif
`ifndef MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK
`define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK                                                        (32'h90)
`define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_MCU_SRAM_ECC_UNC_LOW                              (0)
`define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_MCU_SRAM_ECC_UNC_MASK                             (32'h1)
`define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_NMI_PIN_LOW                                       (1)
`define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_NMI_PIN_MASK                                      (32'h2)
`define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_MCU_SRAM_DMI_AXI_COLLISION_LOW                    (2)
`define MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_MCU_SRAM_DMI_AXI_COLLISION_MASK                   (32'h4)
`endif
`ifndef MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK                                                    (32'h94)
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX0_ECC_UNC_LOW                             (0)
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX0_ECC_UNC_MASK                            (32'h1)
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX1_ECC_UNC_LOW                             (1)
`define MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX1_ECC_UNC_MASK                            (32'h2)
`endif
`ifndef MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK
`define MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK                                                       (32'h98)
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
`define MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK                                                   (32'h9c)
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
`define MCI_REG_INTERNAL_FW_ERROR_FATAL_MASK                                                        (32'ha0)
`endif
`ifndef MCI_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK
`define MCI_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK                                                    (32'ha4)
`endif
`ifndef MCI_REG_WDT_TIMER1_EN
`define MCI_REG_WDT_TIMER1_EN                                                                       (32'hb0)
`define MCI_REG_WDT_TIMER1_EN_TIMER1_EN_LOW                                                         (0)
`define MCI_REG_WDT_TIMER1_EN_TIMER1_EN_MASK                                                        (32'h1)
`endif
`ifndef MCI_REG_WDT_TIMER1_CTRL
`define MCI_REG_WDT_TIMER1_CTRL                                                                     (32'hb4)
`define MCI_REG_WDT_TIMER1_CTRL_TIMER1_RESTART_LOW                                                  (0)
`define MCI_REG_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK                                                 (32'h1)
`endif
`ifndef MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_0
`define MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_0                                                         (32'hb8)
`endif
`ifndef MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_1
`define MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_1                                                         (32'hbc)
`endif
`ifndef MCI_REG_WDT_TIMER2_EN
`define MCI_REG_WDT_TIMER2_EN                                                                       (32'hc0)
`define MCI_REG_WDT_TIMER2_EN_TIMER2_EN_LOW                                                         (0)
`define MCI_REG_WDT_TIMER2_EN_TIMER2_EN_MASK                                                        (32'h1)
`endif
`ifndef MCI_REG_WDT_TIMER2_CTRL
`define MCI_REG_WDT_TIMER2_CTRL                                                                     (32'hc4)
`define MCI_REG_WDT_TIMER2_CTRL_TIMER2_RESTART_LOW                                                  (0)
`define MCI_REG_WDT_TIMER2_CTRL_TIMER2_RESTART_MASK                                                 (32'h1)
`endif
`ifndef MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_0
`define MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_0                                                         (32'hc8)
`endif
`ifndef MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_1
`define MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_1                                                         (32'hcc)
`endif
`ifndef MCI_REG_WDT_STATUS
`define MCI_REG_WDT_STATUS                                                                          (32'hd0)
`define MCI_REG_WDT_STATUS_T1_TIMEOUT_LOW                                                           (0)
`define MCI_REG_WDT_STATUS_T1_TIMEOUT_MASK                                                          (32'h1)
`define MCI_REG_WDT_STATUS_T2_TIMEOUT_LOW                                                           (1)
`define MCI_REG_WDT_STATUS_T2_TIMEOUT_MASK                                                          (32'h2)
`endif
`ifndef MCI_REG_WDT_CFG_0
`define MCI_REG_WDT_CFG_0                                                                           (32'hd4)
`endif
`ifndef MCI_REG_WDT_CFG_1
`define MCI_REG_WDT_CFG_1                                                                           (32'hd8)
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
`ifndef MCI_REG_CPTRA_BOOT_GO
`define MCI_REG_CPTRA_BOOT_GO                                                                       (32'h108)
`define MCI_REG_CPTRA_BOOT_GO_GO_LOW                                                                (0)
`define MCI_REG_CPTRA_BOOT_GO_GO_MASK                                                               (32'h1)
`endif
`ifndef MCI_REG_FW_SRAM_EXEC_REGION_SIZE
`define MCI_REG_FW_SRAM_EXEC_REGION_SIZE                                                            (32'h10c)
`define MCI_REG_FW_SRAM_EXEC_REGION_SIZE_SIZE_LOW                                                   (0)
`define MCI_REG_FW_SRAM_EXEC_REGION_SIZE_SIZE_MASK                                                  (32'hffff)
`endif
`ifndef MCI_REG_MCU_NMI_VECTOR
`define MCI_REG_MCU_NMI_VECTOR                                                                      (32'h110)
`endif
`ifndef MCI_REG_MCU_RESET_VECTOR
`define MCI_REG_MCU_RESET_VECTOR                                                                    (32'h114)
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
`ifndef MCI_REG_FC_FIPS_ZEROZATION
`define MCI_REG_FC_FIPS_ZEROZATION                                                                  (32'h318)
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
`endif
`ifndef MCI_REG_DEBUG_OUT
`define MCI_REG_DEBUG_OUT                                                                           (32'h414)
`endif
`ifndef MCI_REG_SS_DEBUG_INTENT
`define MCI_REG_SS_DEBUG_INTENT                                                                     (32'h418)
`define MCI_REG_SS_DEBUG_INTENT_DEBUG_INTENT_LOW                                                    (0)
`define MCI_REG_SS_DEBUG_INTENT_DEBUG_INTENT_MASK                                                   (32'h1)
`endif
`ifndef MCI_REG_SS_CONFIG_DONE_STICKY
`define MCI_REG_SS_CONFIG_DONE_STICKY                                                               (32'h440)
`define MCI_REG_SS_CONFIG_DONE_STICKY_DONE_LOW                                                      (0)
`define MCI_REG_SS_CONFIG_DONE_STICKY_DONE_MASK                                                     (32'h1)
`endif
`ifndef MCI_REG_SS_CONFIG_DONE
`define MCI_REG_SS_CONFIG_DONE                                                                      (32'h444)
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
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX0_ECC_UNC_EN_LOW                           (2)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX0_ECC_UNC_EN_MASK                          (32'h4)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX1_ECC_UNC_EN_LOW                           (3)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX1_ECC_UNC_EN_MASK                          (32'h8)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_LOW                      (4)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_MASK                     (32'h10)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_LOW                      (5)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_MASK                     (32'h20)
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
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_TARGET_DONE_EN_LOW                       (3)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_TARGET_DONE_EN_MASK                      (32'h8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_TARGET_DONE_EN_LOW                       (4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_TARGET_DONE_EN_MASK                      (32'h10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_CMD_AVAIL_EN_LOW                         (5)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_CMD_AVAIL_EN_MASK                        (32'h20)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_CMD_AVAIL_EN_LOW                         (6)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_CMD_AVAIL_EN_MASK                        (32'h40)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_EN_LOW                    (7)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_EN_MASK                   (32'h80)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_ECC_COR_EN_LOW                           (8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_ECC_COR_EN_MASK                          (32'h100)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_ECC_COR_EN_LOW                           (9)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_ECC_COR_EN_MASK                          (32'h200)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_DEBUG_LOCKED_EN_LOW                            (10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_DEBUG_LOCKED_EN_MASK                           (32'h400)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_SCAN_MODE_EN_LOW                               (11)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_SCAN_MODE_EN_MASK                              (32'h800)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_SOC_REQ_LOCK_EN_LOW                      (12)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_SOC_REQ_LOCK_EN_MASK                     (32'h1000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_SOC_REQ_LOCK_EN_LOW                      (13)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_SOC_REQ_LOCK_EN_MASK                     (32'h2000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_OTP_OPERATION_DONE_EN_LOW                      (14)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_OTP_OPERATION_DONE_EN_MASK                     (32'h4000)
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
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX0_ECC_UNC_STS_LOW                    (2)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX0_ECC_UNC_STS_MASK                   (32'h4)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX1_ECC_UNC_STS_LOW                    (3)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX1_ECC_UNC_STS_MASK                   (32'h8)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_LOW               (4)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK              (32'h10)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_LOW               (5)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_MASK              (32'h20)
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
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_TARGET_DONE_STS_LOW                (3)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_TARGET_DONE_STS_MASK               (32'h8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_TARGET_DONE_STS_LOW                (4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_TARGET_DONE_STS_MASK               (32'h10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_CMD_AVAIL_STS_LOW                  (5)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_CMD_AVAIL_STS_MASK                 (32'h20)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_CMD_AVAIL_STS_LOW                  (6)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_CMD_AVAIL_STS_MASK                 (32'h40)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_STS_LOW             (7)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_STS_MASK            (32'h80)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_ECC_COR_STS_LOW                    (8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_ECC_COR_STS_MASK                   (32'h100)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_ECC_COR_STS_LOW                    (9)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_ECC_COR_STS_MASK                   (32'h200)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_LOW                     (10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK                    (32'h400)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_LOW                        (11)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_MASK                       (32'h800)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_SOC_REQ_LOCK_STS_LOW               (12)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_SOC_REQ_LOCK_STS_MASK              (32'h1000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_SOC_REQ_LOCK_STS_LOW               (13)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_SOC_REQ_LOCK_STS_MASK              (32'h2000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_OTP_OPERATION_DONE_STS_LOW               (14)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_OTP_OPERATION_DONE_STS_MASK              (32'h4000)
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
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX0_ECC_UNC_TRIG_LOW                       (2)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX0_ECC_UNC_TRIG_MASK                      (32'h4)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX1_ECC_UNC_TRIG_LOW                       (3)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX1_ECC_UNC_TRIG_MASK                      (32'h8)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_WDT_TIMER1_TIMEOUT_TRIG_LOW                  (4)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_WDT_TIMER1_TIMEOUT_TRIG_MASK                 (32'h10)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_WDT_TIMER2_TIMEOUT_TRIG_LOW                  (5)
`define MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_WDT_TIMER2_TIMEOUT_TRIG_MASK                 (32'h20)
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
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_TARGET_DONE_TRIG_LOW                   (3)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_TARGET_DONE_TRIG_MASK                  (32'h8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_TARGET_DONE_TRIG_LOW                   (4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_TARGET_DONE_TRIG_MASK                  (32'h10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_CMD_AVAIL_TRIG_LOW                     (5)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_CMD_AVAIL_TRIG_MASK                    (32'h20)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_CMD_AVAIL_TRIG_LOW                     (6)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_CMD_AVAIL_TRIG_MASK                    (32'h40)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_TRIG_LOW                (7)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_TRIG_MASK               (32'h80)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_ECC_COR_TRIG_LOW                       (8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_ECC_COR_TRIG_MASK                      (32'h100)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_ECC_COR_TRIG_LOW                       (9)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_ECC_COR_TRIG_MASK                      (32'h200)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_DEBUG_LOCKED_TRIG_LOW                        (10)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_DEBUG_LOCKED_TRIG_MASK                       (32'h400)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_SCAN_MODE_TRIG_LOW                           (11)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_SCAN_MODE_TRIG_MASK                          (32'h800)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_SOC_REQ_LOCK_TRIG_LOW                  (12)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_SOC_REQ_LOCK_TRIG_MASK                 (32'h1000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_SOC_REQ_LOCK_TRIG_LOW                  (13)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_SOC_REQ_LOCK_TRIG_MASK                 (32'h2000)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_OTP_OPERATION_DONE_TRIG_LOW                  (14)
`define MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_OTP_OPERATION_DONE_TRIG_MASK                 (32'h4000)
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
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R                                      (32'h1104)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R                                      (32'h1108)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R                         (32'h110c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R                                 (32'h1110)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R                                 (32'h1114)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R                                   (32'h1118)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R                                   (32'h111c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R                                   (32'h1120)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R                                   (32'h1124)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R                                   (32'h1128)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R                                   (32'h112c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R                                   (32'h1130)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R                                   (32'h1134)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R                                   (32'h1138)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R                                   (32'h113c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R                                  (32'h1140)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R                                  (32'h1144)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R                                  (32'h1148)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R                                  (32'h114c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R                                  (32'h1150)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R                                  (32'h1154)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R                                  (32'h1158)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R                                  (32'h115c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R                                  (32'h1160)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R                                  (32'h1164)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R                                  (32'h1168)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R                                  (32'h116c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R                                  (32'h1170)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R                                  (32'h1174)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R                                  (32'h1178)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R                                  (32'h117c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R                                  (32'h1180)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R                                  (32'h1184)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R                                  (32'h1188)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R                                  (32'h118c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R                                  (32'h1190)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R                                  (32'h1194)
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
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R                                  (32'h128c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R                                  (32'h1290)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R                                    (32'h1294)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R                                    (32'h1298)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R                               (32'h129c)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R                                      (32'h12a0)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R                                      (32'h12a4)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R                                       (32'h12a8)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R                                          (32'h12ac)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R                                 (32'h12b0)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R                                 (32'h12b4)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_OTP_OPERATION_DONE_INTR_COUNT_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_OTP_OPERATION_DONE_INTR_COUNT_R                                 (32'h12b8)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R                                      (32'h1300)
`define MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_LOW                            (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_MASK                           (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R                                 (32'h1304)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R_PULSE_MASK                      (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R                                 (32'h1308)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R_PULSE_MASK                      (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R                            (32'h130c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_PULSE_LOW                  (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_PULSE_MASK                 (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R                            (32'h1310)
`define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_PULSE_LOW                  (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_PULSE_MASK                 (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R                    (32'h1314)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R_PULSE_LOW          (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R_PULSE_MASK         (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R                              (32'h1318)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R                              (32'h131c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R                              (32'h1320)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R                              (32'h1324)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R                              (32'h1328)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R                              (32'h132c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R                              (32'h1330)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R                              (32'h1334)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R                              (32'h1338)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R                              (32'h133c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R                             (32'h1340)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R                             (32'h1344)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R                             (32'h1348)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R                             (32'h134c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R                             (32'h1350)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R                             (32'h1354)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R                             (32'h1358)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R                             (32'h135c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R                             (32'h1360)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R                             (32'h1364)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R                             (32'h1368)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R                             (32'h136c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R                             (32'h1370)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R                             (32'h1374)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R                             (32'h1378)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R                             (32'h137c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R                             (32'h1380)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R                             (32'h1384)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R                             (32'h1388)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R                             (32'h138c)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R                             (32'h1390)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R                             (32'h1394)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R                              (32'h1398)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R                           (32'h139c)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R_PULSE_LOW                 (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R_PULSE_MASK                (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R                                 (32'h13a0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R_PULSE_MASK                      (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R                          (32'h13a4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R                          (32'h13a8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R                          (32'h13ac)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R                          (32'h13b0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R                          (32'h13b4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R                          (32'h13b8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R                          (32'h13bc)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R                          (32'h13c0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R                          (32'h13c4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R                          (32'h13c8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R                         (32'h13cc)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R                         (32'h13d0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R                         (32'h13d4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R                         (32'h13d8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R                         (32'h13dc)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R                         (32'h13e0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R                         (32'h13e4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R                         (32'h13e8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R                         (32'h13ec)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R                         (32'h13f0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R                         (32'h13f4)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R                         (32'h13f8)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R                         (32'h13fc)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R                         (32'h1400)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R                         (32'h1404)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R                         (32'h1408)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R                         (32'h140c)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R                         (32'h1410)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R                         (32'h1414)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R                         (32'h1418)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R                         (32'h141c)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R                         (32'h1420)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R_PULSE_LOW               (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R_PULSE_MASK              (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R                             (32'h1424)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R                             (32'h1428)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R                               (32'h142c)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_LOW                     (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_MASK                    (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R                               (32'h1430)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_LOW                     (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_MASK                    (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R                          (32'h1434)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_LOW                (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_MASK               (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R                                 (32'h1438)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R_PULSE_MASK                      (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R                                 (32'h143c)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R_PULSE_MASK                      (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R                                  (32'h1440)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R_PULSE_LOW                        (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R_PULSE_MASK                       (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R                                     (32'h1444)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R_PULSE_LOW                           (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R_PULSE_MASK                          (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R                            (32'h1448)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R_PULSE_LOW                  (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R_PULSE_MASK                 (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R                            (32'h144c)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R_PULSE_LOW                  (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R_PULSE_MASK                 (32'h1)
`endif
`ifndef MCI_REG_INTR_BLOCK_RF_NOTIF_OTP_OPERATION_DONE_INTR_COUNT_INCR_R
`define MCI_REG_INTR_BLOCK_RF_NOTIF_OTP_OPERATION_DONE_INTR_COUNT_INCR_R                            (32'h1450)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_OTP_OPERATION_DONE_INTR_COUNT_INCR_R_PULSE_LOW                  (0)
`define MCI_REG_INTR_BLOCK_RF_NOTIF_OTP_OPERATION_DONE_INTR_COUNT_INCR_R_PULSE_MASK                 (32'h1)
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
`ifndef MCU_MBOX0_CSR_MBOX_LOCK
`define MCU_MBOX0_CSR_MBOX_LOCK                                                                     (32'h200000)
`define MCU_MBOX0_CSR_MBOX_LOCK_LOCK_LOW                                                            (0)
`define MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK                                                           (32'h1)
`endif
`ifndef MCU_MBOX0_CSR_MBOX_USER
`define MCU_MBOX0_CSR_MBOX_USER                                                                     (32'h200004)
`endif
`ifndef MCU_MBOX0_CSR_MBOX_TARGET_USER
`define MCU_MBOX0_CSR_MBOX_TARGET_USER                                                              (32'h200008)
`endif
`ifndef MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID
`define MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID                                                        (32'h20000c)
`define MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID_VALID_LOW                                              (0)
`define MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID_VALID_MASK                                             (32'h1)
`endif
`ifndef MCU_MBOX0_CSR_MBOX_CMD
`define MCU_MBOX0_CSR_MBOX_CMD                                                                      (32'h200010)
`endif
`ifndef MCU_MBOX0_CSR_MBOX_DLEN
`define MCU_MBOX0_CSR_MBOX_DLEN                                                                     (32'h200014)
`endif
`ifndef MCU_MBOX0_CSR_MBOX_EXECUTE
`define MCU_MBOX0_CSR_MBOX_EXECUTE                                                                  (32'h200018)
`define MCU_MBOX0_CSR_MBOX_EXECUTE_EXECUTE_LOW                                                      (0)
`define MCU_MBOX0_CSR_MBOX_EXECUTE_EXECUTE_MASK                                                     (32'h1)
`endif
`ifndef MCU_MBOX0_CSR_MBOX_TARGET_STATUS
`define MCU_MBOX0_CSR_MBOX_TARGET_STATUS                                                            (32'h20001c)
`define MCU_MBOX0_CSR_MBOX_TARGET_STATUS_STATUS_LOW                                                 (0)
`define MCU_MBOX0_CSR_MBOX_TARGET_STATUS_STATUS_MASK                                                (32'hf)
`define MCU_MBOX0_CSR_MBOX_TARGET_STATUS_DONE_LOW                                                   (4)
`define MCU_MBOX0_CSR_MBOX_TARGET_STATUS_DONE_MASK                                                  (32'h10)
`endif
`ifndef MCU_MBOX0_CSR_MBOX_CMD_STATUS
`define MCU_MBOX0_CSR_MBOX_CMD_STATUS                                                               (32'h200020)
`define MCU_MBOX0_CSR_MBOX_CMD_STATUS_STATUS_LOW                                                    (0)
`define MCU_MBOX0_CSR_MBOX_CMD_STATUS_STATUS_MASK                                                   (32'hf)
`endif
`ifndef MCU_MBOX0_CSR_MBOX_HW_STATUS
`define MCU_MBOX0_CSR_MBOX_HW_STATUS                                                                (32'h200024)
`define MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_SINGLE_ERROR_LOW                                           (0)
`define MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_SINGLE_ERROR_MASK                                          (32'h1)
`define MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_DOUBLE_ERROR_LOW                                           (1)
`define MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_DOUBLE_ERROR_MASK                                          (32'h2)
`endif
`ifndef MCU_MBOX1_CSR_MBOX_LOCK
`define MCU_MBOX1_CSR_MBOX_LOCK                                                                     (32'h200000)
`define MCU_MBOX1_CSR_MBOX_LOCK_LOCK_LOW                                                            (0)
`define MCU_MBOX1_CSR_MBOX_LOCK_LOCK_MASK                                                           (32'h1)
`endif
`ifndef MCU_MBOX1_CSR_MBOX_USER
`define MCU_MBOX1_CSR_MBOX_USER                                                                     (32'h200004)
`endif
`ifndef MCU_MBOX1_CSR_MBOX_TARGET_USER
`define MCU_MBOX1_CSR_MBOX_TARGET_USER                                                              (32'h200008)
`endif
`ifndef MCU_MBOX1_CSR_MBOX_TARGET_USER_VALID
`define MCU_MBOX1_CSR_MBOX_TARGET_USER_VALID                                                        (32'h20000c)
`define MCU_MBOX1_CSR_MBOX_TARGET_USER_VALID_VALID_LOW                                              (0)
`define MCU_MBOX1_CSR_MBOX_TARGET_USER_VALID_VALID_MASK                                             (32'h1)
`endif
`ifndef MCU_MBOX1_CSR_MBOX_CMD
`define MCU_MBOX1_CSR_MBOX_CMD                                                                      (32'h200010)
`endif
`ifndef MCU_MBOX1_CSR_MBOX_DLEN
`define MCU_MBOX1_CSR_MBOX_DLEN                                                                     (32'h200014)
`endif
`ifndef MCU_MBOX1_CSR_MBOX_EXECUTE
`define MCU_MBOX1_CSR_MBOX_EXECUTE                                                                  (32'h200018)
`define MCU_MBOX1_CSR_MBOX_EXECUTE_EXECUTE_LOW                                                      (0)
`define MCU_MBOX1_CSR_MBOX_EXECUTE_EXECUTE_MASK                                                     (32'h1)
`endif
`ifndef MCU_MBOX1_CSR_MBOX_TARGET_STATUS
`define MCU_MBOX1_CSR_MBOX_TARGET_STATUS                                                            (32'h20001c)
`define MCU_MBOX1_CSR_MBOX_TARGET_STATUS_STATUS_LOW                                                 (0)
`define MCU_MBOX1_CSR_MBOX_TARGET_STATUS_STATUS_MASK                                                (32'hf)
`define MCU_MBOX1_CSR_MBOX_TARGET_STATUS_DONE_LOW                                                   (4)
`define MCU_MBOX1_CSR_MBOX_TARGET_STATUS_DONE_MASK                                                  (32'h10)
`endif
`ifndef MCU_MBOX1_CSR_MBOX_CMD_STATUS
`define MCU_MBOX1_CSR_MBOX_CMD_STATUS                                                               (32'h200020)
`define MCU_MBOX1_CSR_MBOX_CMD_STATUS_STATUS_LOW                                                    (0)
`define MCU_MBOX1_CSR_MBOX_CMD_STATUS_STATUS_MASK                                                   (32'hf)
`endif
`ifndef MCU_MBOX1_CSR_MBOX_HW_STATUS
`define MCU_MBOX1_CSR_MBOX_HW_STATUS                                                                (32'h200024)
`define MCU_MBOX1_CSR_MBOX_HW_STATUS_ECC_SINGLE_ERROR_LOW                                           (0)
`define MCU_MBOX1_CSR_MBOX_HW_STATUS_ECC_SINGLE_ERROR_MASK                                          (32'h1)
`define MCU_MBOX1_CSR_MBOX_HW_STATUS_ECC_DOUBLE_ERROR_LOW                                           (1)
`define MCU_MBOX1_CSR_MBOX_HW_STATUS_ECC_DOUBLE_ERROR_MASK                                          (32'h2)
`endif
`ifndef OTP_CTRL_INTERRUPT_STATE
`define OTP_CTRL_INTERRUPT_STATE                                                                    (32'h0)
`define OTP_CTRL_INTERRUPT_STATE_OTP_OPERATION_DONE_LOW                                             (0)
`define OTP_CTRL_INTERRUPT_STATE_OTP_OPERATION_DONE_MASK                                            (32'h1)
`define OTP_CTRL_INTERRUPT_STATE_OTP_ERROR_LOW                                                      (1)
`define OTP_CTRL_INTERRUPT_STATE_OTP_ERROR_MASK                                                     (32'h2)
`endif
`ifndef OTP_CTRL_INTERRUPT_ENABLE
`define OTP_CTRL_INTERRUPT_ENABLE                                                                   (32'h4)
`define OTP_CTRL_INTERRUPT_ENABLE_OTP_OPERATION_DONE_LOW                                            (0)
`define OTP_CTRL_INTERRUPT_ENABLE_OTP_OPERATION_DONE_MASK                                           (32'h1)
`define OTP_CTRL_INTERRUPT_ENABLE_OTP_ERROR_LOW                                                     (1)
`define OTP_CTRL_INTERRUPT_ENABLE_OTP_ERROR_MASK                                                    (32'h2)
`endif
`ifndef OTP_CTRL_INTERRUPT_TEST
`define OTP_CTRL_INTERRUPT_TEST                                                                     (32'h8)
`define OTP_CTRL_INTERRUPT_TEST_OTP_OPERATION_DONE_LOW                                              (0)
`define OTP_CTRL_INTERRUPT_TEST_OTP_OPERATION_DONE_MASK                                             (32'h1)
`define OTP_CTRL_INTERRUPT_TEST_OTP_ERROR_LOW                                                       (1)
`define OTP_CTRL_INTERRUPT_TEST_OTP_ERROR_MASK                                                      (32'h2)
`endif
`ifndef OTP_CTRL_ALERT_TEST
`define OTP_CTRL_ALERT_TEST                                                                         (32'hc)
`define OTP_CTRL_ALERT_TEST_FATAL_MACR_ERROR_LOW                                                    (0)
`define OTP_CTRL_ALERT_TEST_FATAL_MACR_ERROR_MASK                                                   (32'h1)
`define OTP_CTRL_ALERT_TEST_FATAL_CHECK_ERROR_LOW                                                   (1)
`define OTP_CTRL_ALERT_TEST_FATAL_CHECK_ERROR_MASK                                                  (32'h2)
`define OTP_CTRL_ALERT_TEST_FATAL_BUS_INTEG_ERROR_LOW                                               (2)
`define OTP_CTRL_ALERT_TEST_FATAL_BUS_INTEG_ERROR_MASK                                              (32'h4)
`define OTP_CTRL_ALERT_TEST_FATAL_PRIM_OTP_ALERT_LOW                                                (3)
`define OTP_CTRL_ALERT_TEST_FATAL_PRIM_OTP_ALERT_MASK                                               (32'h8)
`define OTP_CTRL_ALERT_TEST_RECOV_PRIM_OTP_ALERT_LOW                                                (4)
`define OTP_CTRL_ALERT_TEST_RECOV_PRIM_OTP_ALERT_MASK                                               (32'h10)
`endif
`ifndef OTP_CTRL_STATUS
`define OTP_CTRL_STATUS                                                                             (32'h10)
`define OTP_CTRL_STATUS_SECRET_TEST_UNLOCK_PARTITION_ERROR_LOW                                      (0)
`define OTP_CTRL_STATUS_SECRET_TEST_UNLOCK_PARTITION_ERROR_MASK                                     (32'h1)
`define OTP_CTRL_STATUS_SECRET_MANUF_PARTITION_ERROR_LOW                                            (1)
`define OTP_CTRL_STATUS_SECRET_MANUF_PARTITION_ERROR_MASK                                           (32'h2)
`define OTP_CTRL_STATUS_SECRET_PROD_PARTITION_0_ERROR_LOW                                           (2)
`define OTP_CTRL_STATUS_SECRET_PROD_PARTITION_0_ERROR_MASK                                          (32'h4)
`define OTP_CTRL_STATUS_SECRET_PROD_PARTITION_1_ERROR_LOW                                           (3)
`define OTP_CTRL_STATUS_SECRET_PROD_PARTITION_1_ERROR_MASK                                          (32'h8)
`define OTP_CTRL_STATUS_SECRET_PROD_PARTITION_2_ERROR_LOW                                           (4)
`define OTP_CTRL_STATUS_SECRET_PROD_PARTITION_2_ERROR_MASK                                          (32'h10)
`define OTP_CTRL_STATUS_SECRET_PROD_PARTITION_3_ERROR_LOW                                           (5)
`define OTP_CTRL_STATUS_SECRET_PROD_PARTITION_3_ERROR_MASK                                          (32'h20)
`define OTP_CTRL_STATUS_SW_MANUF_PARTITION_ERROR_LOW                                                (6)
`define OTP_CTRL_STATUS_SW_MANUF_PARTITION_ERROR_MASK                                               (32'h40)
`define OTP_CTRL_STATUS_SECRET_LC_TRANSITION_PARTITION_ERROR_LOW                                    (7)
`define OTP_CTRL_STATUS_SECRET_LC_TRANSITION_PARTITION_ERROR_MASK                                   (32'h80)
`define OTP_CTRL_STATUS_SVN_PARTITION_ERROR_LOW                                                     (8)
`define OTP_CTRL_STATUS_SVN_PARTITION_ERROR_MASK                                                    (32'h100)
`define OTP_CTRL_STATUS_VENDOR_TEST_PARTITION_ERROR_LOW                                             (9)
`define OTP_CTRL_STATUS_VENDOR_TEST_PARTITION_ERROR_MASK                                            (32'h200)
`define OTP_CTRL_STATUS_VENDOR_HASHES_MANUF_PARTITION_ERROR_LOW                                     (10)
`define OTP_CTRL_STATUS_VENDOR_HASHES_MANUF_PARTITION_ERROR_MASK                                    (32'h400)
`define OTP_CTRL_STATUS_VENDOR_HASHES_PROD_PARTITION_ERROR_LOW                                      (11)
`define OTP_CTRL_STATUS_VENDOR_HASHES_PROD_PARTITION_ERROR_MASK                                     (32'h800)
`define OTP_CTRL_STATUS_VENDOR_REVOCATIONS_PROD_PARTITION_ERROR_LOW                                 (12)
`define OTP_CTRL_STATUS_VENDOR_REVOCATIONS_PROD_PARTITION_ERROR_MASK                                (32'h1000)
`define OTP_CTRL_STATUS_VENDOR_SECRET_PROD_PARTITION_ERROR_LOW                                      (13)
`define OTP_CTRL_STATUS_VENDOR_SECRET_PROD_PARTITION_ERROR_MASK                                     (32'h2000)
`define OTP_CTRL_STATUS_VENDOR_NON_SECRET_PROD_PARTITION_ERROR_LOW                                  (14)
`define OTP_CTRL_STATUS_VENDOR_NON_SECRET_PROD_PARTITION_ERROR_MASK                                 (32'h4000)
`define OTP_CTRL_STATUS_LIFE_CYCLE_ERROR_LOW                                                        (15)
`define OTP_CTRL_STATUS_LIFE_CYCLE_ERROR_MASK                                                       (32'h8000)
`define OTP_CTRL_STATUS_DAI_ERROR_LOW                                                               (16)
`define OTP_CTRL_STATUS_DAI_ERROR_MASK                                                              (32'h10000)
`define OTP_CTRL_STATUS_LCI_ERROR_LOW                                                               (17)
`define OTP_CTRL_STATUS_LCI_ERROR_MASK                                                              (32'h20000)
`define OTP_CTRL_STATUS_TIMEOUT_ERROR_LOW                                                           (18)
`define OTP_CTRL_STATUS_TIMEOUT_ERROR_MASK                                                          (32'h40000)
`define OTP_CTRL_STATUS_LFSR_FSM_ERROR_LOW                                                          (19)
`define OTP_CTRL_STATUS_LFSR_FSM_ERROR_MASK                                                         (32'h80000)
`define OTP_CTRL_STATUS_SCRAMBLING_FSM_ERROR_LOW                                                    (20)
`define OTP_CTRL_STATUS_SCRAMBLING_FSM_ERROR_MASK                                                   (32'h100000)
`define OTP_CTRL_STATUS_BUS_INTEG_ERROR_LOW                                                         (21)
`define OTP_CTRL_STATUS_BUS_INTEG_ERROR_MASK                                                        (32'h200000)
`define OTP_CTRL_STATUS_DAI_IDLE_LOW                                                                (22)
`define OTP_CTRL_STATUS_DAI_IDLE_MASK                                                               (32'h400000)
`define OTP_CTRL_STATUS_CHECK_PENDING_LOW                                                           (23)
`define OTP_CTRL_STATUS_CHECK_PENDING_MASK                                                          (32'h800000)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_0
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_0                                                             (32'h14)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_0_ERR_CODE_LOW                                                (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_0_ERR_CODE_MASK                                               (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_1
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_1                                                             (32'h18)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_1_ERR_CODE_LOW                                                (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_1_ERR_CODE_MASK                                               (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_2
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_2                                                             (32'h1c)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_2_ERR_CODE_LOW                                                (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_2_ERR_CODE_MASK                                               (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_3
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_3                                                             (32'h20)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_3_ERR_CODE_LOW                                                (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_3_ERR_CODE_MASK                                               (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_4
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_4                                                             (32'h24)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_4_ERR_CODE_LOW                                                (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_4_ERR_CODE_MASK                                               (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_5
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_5                                                             (32'h28)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_5_ERR_CODE_LOW                                                (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_5_ERR_CODE_MASK                                               (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_6
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_6                                                             (32'h2c)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_6_ERR_CODE_LOW                                                (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_6_ERR_CODE_MASK                                               (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_7
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_7                                                             (32'h30)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_7_ERR_CODE_LOW                                                (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_7_ERR_CODE_MASK                                               (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_8
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_8                                                             (32'h34)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_8_ERR_CODE_LOW                                                (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_8_ERR_CODE_MASK                                               (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_9
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_9                                                             (32'h38)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_9_ERR_CODE_LOW                                                (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_9_ERR_CODE_MASK                                               (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_10
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_10                                                            (32'h3c)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_10_ERR_CODE_LOW                                               (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_10_ERR_CODE_MASK                                              (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_11
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_11                                                            (32'h40)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_11_ERR_CODE_LOW                                               (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_11_ERR_CODE_MASK                                              (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_12
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_12                                                            (32'h44)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_12_ERR_CODE_LOW                                               (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_12_ERR_CODE_MASK                                              (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_13
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_13                                                            (32'h48)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_13_ERR_CODE_LOW                                               (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_13_ERR_CODE_MASK                                              (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_14
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_14                                                            (32'h4c)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_14_ERR_CODE_LOW                                               (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_14_ERR_CODE_MASK                                              (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_15
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_15                                                            (32'h50)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_15_ERR_CODE_LOW                                               (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_15_ERR_CODE_MASK                                              (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_16
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_16                                                            (32'h54)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_16_ERR_CODE_LOW                                               (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_16_ERR_CODE_MASK                                              (32'h7)
`endif
`ifndef OTP_CTRL_ERR_CODE_RF_ERR_CODE_17
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_17                                                            (32'h58)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_17_ERR_CODE_LOW                                               (0)
`define OTP_CTRL_ERR_CODE_RF_ERR_CODE_17_ERR_CODE_MASK                                              (32'h7)
`endif
`ifndef OTP_CTRL_DIRECT_ACCESS_REGWEN
`define OTP_CTRL_DIRECT_ACCESS_REGWEN                                                               (32'h5c)
`define OTP_CTRL_DIRECT_ACCESS_REGWEN_REGWEN_LOW                                                    (0)
`define OTP_CTRL_DIRECT_ACCESS_REGWEN_REGWEN_MASK                                                   (32'h1)
`endif
`ifndef OTP_CTRL_DIRECT_ACCESS_CMD
`define OTP_CTRL_DIRECT_ACCESS_CMD                                                                  (32'h60)
`define OTP_CTRL_DIRECT_ACCESS_CMD_RD_LOW                                                           (0)
`define OTP_CTRL_DIRECT_ACCESS_CMD_RD_MASK                                                          (32'h1)
`define OTP_CTRL_DIRECT_ACCESS_CMD_WR_LOW                                                           (1)
`define OTP_CTRL_DIRECT_ACCESS_CMD_WR_MASK                                                          (32'h2)
`define OTP_CTRL_DIRECT_ACCESS_CMD_DIGEST_LOW                                                       (2)
`define OTP_CTRL_DIRECT_ACCESS_CMD_DIGEST_MASK                                                      (32'h4)
`endif
`ifndef OTP_CTRL_DIRECT_ACCESS_ADDRESS
`define OTP_CTRL_DIRECT_ACCESS_ADDRESS                                                              (32'h64)
`define OTP_CTRL_DIRECT_ACCESS_ADDRESS_ADDRESS_LOW                                                  (0)
`define OTP_CTRL_DIRECT_ACCESS_ADDRESS_ADDRESS_MASK                                                 (32'hfff)
`endif
`ifndef OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_0
`define OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_0                                                 (32'h68)
`endif
`ifndef OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_1
`define OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_1                                                 (32'h6c)
`endif
`ifndef OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_0
`define OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_0                                                 (32'h70)
`endif
`ifndef OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_1
`define OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_1                                                 (32'h74)
`endif
`ifndef OTP_CTRL_CHECK_TRIGGER_REGWEN
`define OTP_CTRL_CHECK_TRIGGER_REGWEN                                                               (32'h78)
`define OTP_CTRL_CHECK_TRIGGER_REGWEN_REGWEN_LOW                                                    (0)
`define OTP_CTRL_CHECK_TRIGGER_REGWEN_REGWEN_MASK                                                   (32'h1)
`endif
`ifndef OTP_CTRL_CHECK_TRIGGER
`define OTP_CTRL_CHECK_TRIGGER                                                                      (32'h7c)
`define OTP_CTRL_CHECK_TRIGGER_INTEGRITY_LOW                                                        (0)
`define OTP_CTRL_CHECK_TRIGGER_INTEGRITY_MASK                                                       (32'h1)
`define OTP_CTRL_CHECK_TRIGGER_CONSISTENCY_LOW                                                      (1)
`define OTP_CTRL_CHECK_TRIGGER_CONSISTENCY_MASK                                                     (32'h2)
`endif
`ifndef OTP_CTRL_CHECK_REGWEN
`define OTP_CTRL_CHECK_REGWEN                                                                       (32'h80)
`define OTP_CTRL_CHECK_REGWEN_REGWEN_LOW                                                            (0)
`define OTP_CTRL_CHECK_REGWEN_REGWEN_MASK                                                           (32'h1)
`endif
`ifndef OTP_CTRL_CHECK_TIMEOUT
`define OTP_CTRL_CHECK_TIMEOUT                                                                      (32'h84)
`endif
`ifndef OTP_CTRL_INTEGRITY_CHECK_PERIOD
`define OTP_CTRL_INTEGRITY_CHECK_PERIOD                                                             (32'h88)
`endif
`ifndef OTP_CTRL_CONSISTENCY_CHECK_PERIOD
`define OTP_CTRL_CONSISTENCY_CHECK_PERIOD                                                           (32'h8c)
`endif
`ifndef OTP_CTRL_SW_MANUF_PARTITION_READ_LOCK
`define OTP_CTRL_SW_MANUF_PARTITION_READ_LOCK                                                       (32'h90)
`define OTP_CTRL_SW_MANUF_PARTITION_READ_LOCK_READ_LOCK_LOW                                         (0)
`define OTP_CTRL_SW_MANUF_PARTITION_READ_LOCK_READ_LOCK_MASK                                        (32'h1)
`endif
`ifndef OTP_CTRL_SVN_PARTITION_READ_LOCK
`define OTP_CTRL_SVN_PARTITION_READ_LOCK                                                            (32'h94)
`define OTP_CTRL_SVN_PARTITION_READ_LOCK_READ_LOCK_LOW                                              (0)
`define OTP_CTRL_SVN_PARTITION_READ_LOCK_READ_LOCK_MASK                                             (32'h1)
`endif
`ifndef OTP_CTRL_VENDOR_TEST_PARTITION_READ_LOCK
`define OTP_CTRL_VENDOR_TEST_PARTITION_READ_LOCK                                                    (32'h98)
`define OTP_CTRL_VENDOR_TEST_PARTITION_READ_LOCK_READ_LOCK_LOW                                      (0)
`define OTP_CTRL_VENDOR_TEST_PARTITION_READ_LOCK_READ_LOCK_MASK                                     (32'h1)
`endif
`ifndef OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_READ_LOCK
`define OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_READ_LOCK                                            (32'h9c)
`define OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_READ_LOCK_READ_LOCK_LOW                              (0)
`define OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_READ_LOCK_READ_LOCK_MASK                             (32'h1)
`endif
`ifndef OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_READ_LOCK
`define OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_READ_LOCK                                             (32'ha0)
`define OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_READ_LOCK_READ_LOCK_LOW                               (0)
`define OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_READ_LOCK_READ_LOCK_MASK                              (32'h1)
`endif
`ifndef OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK
`define OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK                                        (32'ha4)
`define OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK_READ_LOCK_LOW                          (0)
`define OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK_READ_LOCK_MASK                         (32'h1)
`endif
`ifndef OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK
`define OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK                                         (32'ha8)
`define OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK_READ_LOCK_LOW                           (0)
`define OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK_READ_LOCK_MASK                          (32'h1)
`endif
`ifndef OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK
`define OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK                                                       (32'hac)
`endif
`ifndef OTP_CTRL_SECRET_TEST_UNLOCK_PARTITION_DIGEST_DIGEST_0
`define OTP_CTRL_SECRET_TEST_UNLOCK_PARTITION_DIGEST_DIGEST_0                                       (32'hb0)
`endif
`ifndef OTP_CTRL_SECRET_TEST_UNLOCK_PARTITION_DIGEST_DIGEST_1
`define OTP_CTRL_SECRET_TEST_UNLOCK_PARTITION_DIGEST_DIGEST_1                                       (32'hb4)
`endif
`ifndef OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_0
`define OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_0                                             (32'hb8)
`endif
`ifndef OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_1
`define OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_1                                             (32'hbc)
`endif
`ifndef OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_0
`define OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_0                                            (32'hc0)
`endif
`ifndef OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_1
`define OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_1                                            (32'hc4)
`endif
`ifndef OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_DIGEST_0
`define OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_DIGEST_0                                            (32'hc8)
`endif
`ifndef OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_DIGEST_1
`define OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_DIGEST_1                                            (32'hcc)
`endif
`ifndef OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_DIGEST_0
`define OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_DIGEST_0                                            (32'hd0)
`endif
`ifndef OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_DIGEST_1
`define OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_DIGEST_1                                            (32'hd4)
`endif
`ifndef OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_DIGEST_0
`define OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_DIGEST_0                                            (32'hd8)
`endif
`ifndef OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_DIGEST_1
`define OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_DIGEST_1                                            (32'hdc)
`endif
`ifndef OTP_CTRL_SW_MANUF_PARTITION_DIGEST_DIGEST_0
`define OTP_CTRL_SW_MANUF_PARTITION_DIGEST_DIGEST_0                                                 (32'he0)
`endif
`ifndef OTP_CTRL_SW_MANUF_PARTITION_DIGEST_DIGEST_1
`define OTP_CTRL_SW_MANUF_PARTITION_DIGEST_DIGEST_1                                                 (32'he4)
`endif
`ifndef OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_DIGEST_0
`define OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_DIGEST_0                                     (32'he8)
`endif
`ifndef OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_DIGEST_1
`define OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_DIGEST_1                                     (32'hec)
`endif
`ifndef OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_DIGEST_0
`define OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_DIGEST_0                                              (32'hf0)
`endif
`ifndef OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_DIGEST_1
`define OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_DIGEST_1                                              (32'hf4)
`endif
`ifndef OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_DIGEST_0
`define OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_DIGEST_0                                      (32'hf8)
`endif
`ifndef OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_DIGEST_1
`define OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_DIGEST_1                                      (32'hfc)
`endif
`ifndef OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_DIGEST_0
`define OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_DIGEST_0                                       (32'h100)
`endif
`ifndef OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_DIGEST_1
`define OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_DIGEST_1                                       (32'h104)
`endif
`ifndef OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_DIGEST_0
`define OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_DIGEST_0                                  (32'h108)
`endif
`ifndef OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_DIGEST_1
`define OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_DIGEST_1                                  (32'h10c)
`endif
`ifndef OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_0
`define OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_0                                       (32'h110)
`endif
`ifndef OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_1
`define OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_1                                       (32'h114)
`endif
`ifndef OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_DIGEST_0
`define OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_DIGEST_0                                   (32'h118)
`endif
`ifndef OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_DIGEST_1
`define OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_DIGEST_1                                   (32'h11c)
`endif
`ifndef OTP_CTRL_CSR0
`define OTP_CTRL_CSR0                                                                               (32'h120)
`define OTP_CTRL_CSR0_FIELD0_LOW                                                                    (0)
`define OTP_CTRL_CSR0_FIELD0_MASK                                                                   (32'h1)
`define OTP_CTRL_CSR0_FIELD1_LOW                                                                    (1)
`define OTP_CTRL_CSR0_FIELD1_MASK                                                                   (32'h2)
`define OTP_CTRL_CSR0_FIELD2_LOW                                                                    (2)
`define OTP_CTRL_CSR0_FIELD2_MASK                                                                   (32'h4)
`define OTP_CTRL_CSR0_FIELD3_LOW                                                                    (4)
`define OTP_CTRL_CSR0_FIELD3_MASK                                                                   (32'h3ff0)
`define OTP_CTRL_CSR0_FIELD4_LOW                                                                    (16)
`define OTP_CTRL_CSR0_FIELD4_MASK                                                                   (32'h7ff0000)
`endif
`ifndef OTP_CTRL_CSR1
`define OTP_CTRL_CSR1                                                                               (32'h124)
`define OTP_CTRL_CSR1_FIELD0_LOW                                                                    (0)
`define OTP_CTRL_CSR1_FIELD0_MASK                                                                   (32'h7f)
`define OTP_CTRL_CSR1_FIELD1_LOW                                                                    (7)
`define OTP_CTRL_CSR1_FIELD1_MASK                                                                   (32'h80)
`define OTP_CTRL_CSR1_FIELD2_LOW                                                                    (8)
`define OTP_CTRL_CSR1_FIELD2_MASK                                                                   (32'h7f00)
`define OTP_CTRL_CSR1_FIELD3_LOW                                                                    (15)
`define OTP_CTRL_CSR1_FIELD3_MASK                                                                   (32'h8000)
`define OTP_CTRL_CSR1_FIELD4_LOW                                                                    (16)
`define OTP_CTRL_CSR1_FIELD4_MASK                                                                   (32'hffff0000)
`endif
`ifndef OTP_CTRL_CSR2
`define OTP_CTRL_CSR2                                                                               (32'h128)
`define OTP_CTRL_CSR2_FIELD0_LOW                                                                    (0)
`define OTP_CTRL_CSR2_FIELD0_MASK                                                                   (32'h1)
`endif
`ifndef OTP_CTRL_CSR3
`define OTP_CTRL_CSR3                                                                               (32'h12c)
`define OTP_CTRL_CSR3_FIELD0_LOW                                                                    (0)
`define OTP_CTRL_CSR3_FIELD0_MASK                                                                   (32'h7)
`define OTP_CTRL_CSR3_FIELD1_LOW                                                                    (4)
`define OTP_CTRL_CSR3_FIELD1_MASK                                                                   (32'h3ff0)
`define OTP_CTRL_CSR3_FIELD2_LOW                                                                    (16)
`define OTP_CTRL_CSR3_FIELD2_MASK                                                                   (32'h10000)
`define OTP_CTRL_CSR3_FIELD3_LOW                                                                    (17)
`define OTP_CTRL_CSR3_FIELD3_MASK                                                                   (32'h20000)
`define OTP_CTRL_CSR3_FIELD4_LOW                                                                    (18)
`define OTP_CTRL_CSR3_FIELD4_MASK                                                                   (32'h40000)
`define OTP_CTRL_CSR3_FIELD5_LOW                                                                    (19)
`define OTP_CTRL_CSR3_FIELD5_MASK                                                                   (32'h80000)
`define OTP_CTRL_CSR3_FIELD6_LOW                                                                    (20)
`define OTP_CTRL_CSR3_FIELD6_MASK                                                                   (32'h100000)
`define OTP_CTRL_CSR3_FIELD7_LOW                                                                    (21)
`define OTP_CTRL_CSR3_FIELD7_MASK                                                                   (32'h200000)
`define OTP_CTRL_CSR3_FIELD8_LOW                                                                    (22)
`define OTP_CTRL_CSR3_FIELD8_MASK                                                                   (32'h400000)
`endif
`ifndef OTP_CTRL_CSR4
`define OTP_CTRL_CSR4                                                                               (32'h130)
`define OTP_CTRL_CSR4_FIELD0_LOW                                                                    (0)
`define OTP_CTRL_CSR4_FIELD0_MASK                                                                   (32'h3ff)
`define OTP_CTRL_CSR4_FIELD1_LOW                                                                    (12)
`define OTP_CTRL_CSR4_FIELD1_MASK                                                                   (32'h1000)
`define OTP_CTRL_CSR4_FIELD2_LOW                                                                    (13)
`define OTP_CTRL_CSR4_FIELD2_MASK                                                                   (32'h2000)
`define OTP_CTRL_CSR4_FIELD3_LOW                                                                    (14)
`define OTP_CTRL_CSR4_FIELD3_MASK                                                                   (32'h4000)
`endif
`ifndef OTP_CTRL_CSR5
`define OTP_CTRL_CSR5                                                                               (32'h134)
`define OTP_CTRL_CSR5_FIELD0_LOW                                                                    (0)
`define OTP_CTRL_CSR5_FIELD0_MASK                                                                   (32'h3f)
`define OTP_CTRL_CSR5_FIELD1_LOW                                                                    (6)
`define OTP_CTRL_CSR5_FIELD1_MASK                                                                   (32'hc0)
`define OTP_CTRL_CSR5_FIELD2_LOW                                                                    (8)
`define OTP_CTRL_CSR5_FIELD2_MASK                                                                   (32'h100)
`define OTP_CTRL_CSR5_FIELD3_LOW                                                                    (9)
`define OTP_CTRL_CSR5_FIELD3_MASK                                                                   (32'he00)
`define OTP_CTRL_CSR5_FIELD4_LOW                                                                    (12)
`define OTP_CTRL_CSR5_FIELD4_MASK                                                                   (32'h1000)
`define OTP_CTRL_CSR5_FIELD5_LOW                                                                    (13)
`define OTP_CTRL_CSR5_FIELD5_MASK                                                                   (32'h2000)
`define OTP_CTRL_CSR5_FIELD6_LOW                                                                    (16)
`define OTP_CTRL_CSR5_FIELD6_MASK                                                                   (32'hffff0000)
`endif
`ifndef OTP_CTRL_CSR6
`define OTP_CTRL_CSR6                                                                               (32'h138)
`define OTP_CTRL_CSR6_FIELD0_LOW                                                                    (0)
`define OTP_CTRL_CSR6_FIELD0_MASK                                                                   (32'h3ff)
`define OTP_CTRL_CSR6_FIELD1_LOW                                                                    (11)
`define OTP_CTRL_CSR6_FIELD1_MASK                                                                   (32'h800)
`define OTP_CTRL_CSR6_FIELD2_LOW                                                                    (12)
`define OTP_CTRL_CSR6_FIELD2_MASK                                                                   (32'h1000)
`define OTP_CTRL_CSR6_FIELD3_LOW                                                                    (16)
`define OTP_CTRL_CSR6_FIELD3_MASK                                                                   (32'hffff0000)
`endif
`ifndef OTP_CTRL_CSR7
`define OTP_CTRL_CSR7                                                                               (32'h13c)
`define OTP_CTRL_CSR7_FIELD0_LOW                                                                    (0)
`define OTP_CTRL_CSR7_FIELD0_MASK                                                                   (32'h3f)
`define OTP_CTRL_CSR7_FIELD1_LOW                                                                    (8)
`define OTP_CTRL_CSR7_FIELD1_MASK                                                                   (32'h700)
`define OTP_CTRL_CSR7_FIELD2_LOW                                                                    (14)
`define OTP_CTRL_CSR7_FIELD2_MASK                                                                   (32'h4000)
`define OTP_CTRL_CSR7_FIELD3_LOW                                                                    (15)
`define OTP_CTRL_CSR7_FIELD3_MASK                                                                   (32'h8000)
`endif
`ifndef LC_CTRL_ALERT_TEST
`define LC_CTRL_ALERT_TEST                                                                          (32'h0)
`define LC_CTRL_ALERT_TEST_FATAL_PROG_ERROR_LOW                                                     (0)
`define LC_CTRL_ALERT_TEST_FATAL_PROG_ERROR_MASK                                                    (32'h1)
`define LC_CTRL_ALERT_TEST_FATAL_STATE_ERROR_LOW                                                    (1)
`define LC_CTRL_ALERT_TEST_FATAL_STATE_ERROR_MASK                                                   (32'h2)
`define LC_CTRL_ALERT_TEST_FATAL_BUS_INTEG_ERROR_LOW                                                (2)
`define LC_CTRL_ALERT_TEST_FATAL_BUS_INTEG_ERROR_MASK                                               (32'h4)
`endif
`ifndef LC_CTRL_STATUS
`define LC_CTRL_STATUS                                                                              (32'h4)
`define LC_CTRL_STATUS_INITIALIZED_LOW                                                              (0)
`define LC_CTRL_STATUS_INITIALIZED_MASK                                                             (32'h1)
`define LC_CTRL_STATUS_READY_LOW                                                                    (1)
`define LC_CTRL_STATUS_READY_MASK                                                                   (32'h2)
`define LC_CTRL_STATUS_EXT_CLOCK_SWITCHED_LOW                                                       (2)
`define LC_CTRL_STATUS_EXT_CLOCK_SWITCHED_MASK                                                      (32'h4)
`define LC_CTRL_STATUS_TRANSITION_SUCCESSFUL_LOW                                                    (3)
`define LC_CTRL_STATUS_TRANSITION_SUCCESSFUL_MASK                                                   (32'h8)
`define LC_CTRL_STATUS_TRANSITION_COUNT_ERROR_LOW                                                   (4)
`define LC_CTRL_STATUS_TRANSITION_COUNT_ERROR_MASK                                                  (32'h10)
`define LC_CTRL_STATUS_TRANSITION_ERROR_LOW                                                         (5)
`define LC_CTRL_STATUS_TRANSITION_ERROR_MASK                                                        (32'h20)
`define LC_CTRL_STATUS_TOKEN_ERROR_LOW                                                              (6)
`define LC_CTRL_STATUS_TOKEN_ERROR_MASK                                                             (32'h40)
`define LC_CTRL_STATUS_FLASH_RMA_ERROR_LOW                                                          (7)
`define LC_CTRL_STATUS_FLASH_RMA_ERROR_MASK                                                         (32'h80)
`define LC_CTRL_STATUS_OTP_ERROR_LOW                                                                (8)
`define LC_CTRL_STATUS_OTP_ERROR_MASK                                                               (32'h100)
`define LC_CTRL_STATUS_STATE_ERROR_LOW                                                              (9)
`define LC_CTRL_STATUS_STATE_ERROR_MASK                                                             (32'h200)
`define LC_CTRL_STATUS_BUS_INTEG_ERROR_LOW                                                          (10)
`define LC_CTRL_STATUS_BUS_INTEG_ERROR_MASK                                                         (32'h400)
`define LC_CTRL_STATUS_OTP_PARTITION_ERROR_LOW                                                      (11)
`define LC_CTRL_STATUS_OTP_PARTITION_ERROR_MASK                                                     (32'h800)
`endif
`ifndef LC_CTRL_CLAIM_TRANSITION_IF_REGWEN
`define LC_CTRL_CLAIM_TRANSITION_IF_REGWEN                                                          (32'h8)
`define LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_REGWEN_LOW                                               (0)
`define LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_REGWEN_MASK                                              (32'h1)
`endif
`ifndef LC_CTRL_CLAIM_TRANSITION_IF
`define LC_CTRL_CLAIM_TRANSITION_IF                                                                 (32'hc)
`define LC_CTRL_CLAIM_TRANSITION_IF_MUTEX_LOW                                                       (0)
`define LC_CTRL_CLAIM_TRANSITION_IF_MUTEX_MASK                                                      (32'hff)
`endif
`ifndef LC_CTRL_TRANSITION_REGWEN
`define LC_CTRL_TRANSITION_REGWEN                                                                   (32'h10)
`define LC_CTRL_TRANSITION_REGWEN_REGWEN_LOW                                                        (0)
`define LC_CTRL_TRANSITION_REGWEN_REGWEN_MASK                                                       (32'h1)
`endif
`ifndef LC_CTRL_TRANSITION_CMD
`define LC_CTRL_TRANSITION_CMD                                                                      (32'h14)
`define LC_CTRL_TRANSITION_CMD_START_LOW                                                            (0)
`define LC_CTRL_TRANSITION_CMD_START_MASK                                                           (32'h1)
`endif
`ifndef LC_CTRL_TRANSITION_CTRL
`define LC_CTRL_TRANSITION_CTRL                                                                     (32'h18)
`define LC_CTRL_TRANSITION_CTRL_EXT_CLOCK_EN_LOW                                                    (0)
`define LC_CTRL_TRANSITION_CTRL_EXT_CLOCK_EN_MASK                                                   (32'h1)
`define LC_CTRL_TRANSITION_CTRL_VOLATILE_RAW_UNLOCK_LOW                                             (1)
`define LC_CTRL_TRANSITION_CTRL_VOLATILE_RAW_UNLOCK_MASK                                            (32'h2)
`endif
`ifndef LC_CTRL_TRANSITION_TOKEN_0
`define LC_CTRL_TRANSITION_TOKEN_0                                                                  (32'h1c)
`endif
`ifndef LC_CTRL_TRANSITION_TOKEN_1
`define LC_CTRL_TRANSITION_TOKEN_1                                                                  (32'h20)
`endif
`ifndef LC_CTRL_TRANSITION_TOKEN_2
`define LC_CTRL_TRANSITION_TOKEN_2                                                                  (32'h24)
`endif
`ifndef LC_CTRL_TRANSITION_TOKEN_3
`define LC_CTRL_TRANSITION_TOKEN_3                                                                  (32'h28)
`endif
`ifndef LC_CTRL_TRANSITION_TARGET
`define LC_CTRL_TRANSITION_TARGET                                                                   (32'h2c)
`define LC_CTRL_TRANSITION_TARGET_STATE_LOW                                                         (0)
`define LC_CTRL_TRANSITION_TARGET_STATE_MASK                                                        (32'h3fffffff)
`endif
`ifndef LC_CTRL_OTP_VENDOR_TEST_CTRL
`define LC_CTRL_OTP_VENDOR_TEST_CTRL                                                                (32'h30)
`endif
`ifndef LC_CTRL_OTP_VENDOR_TEST_STATUS
`define LC_CTRL_OTP_VENDOR_TEST_STATUS                                                              (32'h34)
`endif
`ifndef LC_CTRL_LC_STATE
`define LC_CTRL_LC_STATE                                                                            (32'h38)
`define LC_CTRL_LC_STATE_STATE_LOW                                                                  (0)
`define LC_CTRL_LC_STATE_STATE_MASK                                                                 (32'h3fffffff)
`endif
`ifndef LC_CTRL_LC_TRANSITION_CNT
`define LC_CTRL_LC_TRANSITION_CNT                                                                   (32'h3c)
`define LC_CTRL_LC_TRANSITION_CNT_CNT_LOW                                                           (0)
`define LC_CTRL_LC_TRANSITION_CNT_CNT_MASK                                                          (32'h1f)
`endif
`ifndef LC_CTRL_LC_ID_STATE
`define LC_CTRL_LC_ID_STATE                                                                         (32'h40)
`endif
`ifndef LC_CTRL_HW_REVISION0
`define LC_CTRL_HW_REVISION0                                                                        (32'h44)
`define LC_CTRL_HW_REVISION0_PRODUCT_ID_LOW                                                         (0)
`define LC_CTRL_HW_REVISION0_PRODUCT_ID_MASK                                                        (32'hffff)
`define LC_CTRL_HW_REVISION0_SILICON_CREATOR_ID_LOW                                                 (16)
`define LC_CTRL_HW_REVISION0_SILICON_CREATOR_ID_MASK                                                (32'hffff0000)
`endif
`ifndef LC_CTRL_HW_REVISION1
`define LC_CTRL_HW_REVISION1                                                                        (32'h48)
`define LC_CTRL_HW_REVISION1_REVISION_ID_LOW                                                        (0)
`define LC_CTRL_HW_REVISION1_REVISION_ID_MASK                                                       (32'hff)
`define LC_CTRL_HW_REVISION1_RESERVED_LOW                                                           (8)
`define LC_CTRL_HW_REVISION1_RESERVED_MASK                                                          (32'hffffff00)
`endif
`ifndef LC_CTRL_DEVICE_ID_0
`define LC_CTRL_DEVICE_ID_0                                                                         (32'h4c)
`endif
`ifndef LC_CTRL_DEVICE_ID_1
`define LC_CTRL_DEVICE_ID_1                                                                         (32'h50)
`endif
`ifndef LC_CTRL_DEVICE_ID_2
`define LC_CTRL_DEVICE_ID_2                                                                         (32'h54)
`endif
`ifndef LC_CTRL_DEVICE_ID_3
`define LC_CTRL_DEVICE_ID_3                                                                         (32'h58)
`endif
`ifndef LC_CTRL_DEVICE_ID_4
`define LC_CTRL_DEVICE_ID_4                                                                         (32'h5c)
`endif
`ifndef LC_CTRL_DEVICE_ID_5
`define LC_CTRL_DEVICE_ID_5                                                                         (32'h60)
`endif
`ifndef LC_CTRL_DEVICE_ID_6
`define LC_CTRL_DEVICE_ID_6                                                                         (32'h64)
`endif
`ifndef LC_CTRL_DEVICE_ID_7
`define LC_CTRL_DEVICE_ID_7                                                                         (32'h68)
`endif
`ifndef LC_CTRL_MANUF_STATE_0
`define LC_CTRL_MANUF_STATE_0                                                                       (32'h6c)
`endif
`ifndef LC_CTRL_MANUF_STATE_1
`define LC_CTRL_MANUF_STATE_1                                                                       (32'h70)
`endif
`ifndef LC_CTRL_MANUF_STATE_2
`define LC_CTRL_MANUF_STATE_2                                                                       (32'h74)
`endif
`ifndef LC_CTRL_MANUF_STATE_3
`define LC_CTRL_MANUF_STATE_3                                                                       (32'h78)
`endif
`ifndef LC_CTRL_MANUF_STATE_4
`define LC_CTRL_MANUF_STATE_4                                                                       (32'h7c)
`endif
`ifndef LC_CTRL_MANUF_STATE_5
`define LC_CTRL_MANUF_STATE_5                                                                       (32'h80)
`endif
`ifndef LC_CTRL_MANUF_STATE_6
`define LC_CTRL_MANUF_STATE_6                                                                       (32'h84)
`endif
`ifndef LC_CTRL_MANUF_STATE_7
`define LC_CTRL_MANUF_STATE_7                                                                       (32'h88)
`endif
`ifndef MBOX_CSR_MBOX_LOCK
`define MBOX_CSR_MBOX_LOCK                                                                          (32'h0)
`define MBOX_CSR_MBOX_LOCK_LOCK_LOW                                                                 (0)
`define MBOX_CSR_MBOX_LOCK_LOCK_MASK                                                                (32'h1)
`endif
`ifndef MBOX_CSR_MBOX_USER
`define MBOX_CSR_MBOX_USER                                                                          (32'h4)
`endif
`ifndef MBOX_CSR_MBOX_CMD
`define MBOX_CSR_MBOX_CMD                                                                           (32'h8)
`endif
`ifndef MBOX_CSR_MBOX_DLEN
`define MBOX_CSR_MBOX_DLEN                                                                          (32'hc)
`endif
`ifndef MBOX_CSR_MBOX_DATAIN
`define MBOX_CSR_MBOX_DATAIN                                                                        (32'h10)
`endif
`ifndef MBOX_CSR_MBOX_DATAOUT
`define MBOX_CSR_MBOX_DATAOUT                                                                       (32'h14)
`endif
`ifndef MBOX_CSR_MBOX_EXECUTE
`define MBOX_CSR_MBOX_EXECUTE                                                                       (32'h18)
`define MBOX_CSR_MBOX_EXECUTE_EXECUTE_LOW                                                           (0)
`define MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK                                                          (32'h1)
`endif
`ifndef MBOX_CSR_MBOX_STATUS
`define MBOX_CSR_MBOX_STATUS                                                                        (32'h1c)
`define MBOX_CSR_MBOX_STATUS_STATUS_LOW                                                             (0)
`define MBOX_CSR_MBOX_STATUS_STATUS_MASK                                                            (32'hf)
`define MBOX_CSR_MBOX_STATUS_ECC_SINGLE_ERROR_LOW                                                   (4)
`define MBOX_CSR_MBOX_STATUS_ECC_SINGLE_ERROR_MASK                                                  (32'h10)
`define MBOX_CSR_MBOX_STATUS_ECC_DOUBLE_ERROR_LOW                                                   (5)
`define MBOX_CSR_MBOX_STATUS_ECC_DOUBLE_ERROR_MASK                                                  (32'h20)
`define MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW                                                        (6)
`define MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK                                                       (32'h1c0)
`define MBOX_CSR_MBOX_STATUS_SOC_HAS_LOCK_LOW                                                       (9)
`define MBOX_CSR_MBOX_STATUS_SOC_HAS_LOCK_MASK                                                      (32'h200)
`define MBOX_CSR_MBOX_STATUS_MBOX_RDPTR_LOW                                                         (10)
`define MBOX_CSR_MBOX_STATUS_MBOX_RDPTR_MASK                                                        (32'h3fffc00)
`define MBOX_CSR_MBOX_STATUS_TAP_HAS_LOCK_LOW                                                       (26)
`define MBOX_CSR_MBOX_STATUS_TAP_HAS_LOCK_MASK                                                      (32'h4000000)
`endif
`ifndef MBOX_CSR_MBOX_UNLOCK
`define MBOX_CSR_MBOX_UNLOCK                                                                        (32'h20)
`define MBOX_CSR_MBOX_UNLOCK_UNLOCK_LOW                                                             (0)
`define MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK                                                            (32'h1)
`endif
`ifndef MBOX_CSR_TAP_MODE
`define MBOX_CSR_TAP_MODE                                                                           (32'h24)
`define MBOX_CSR_TAP_MODE_ENABLED_LOW                                                               (0)
`define MBOX_CSR_TAP_MODE_ENABLED_MASK                                                              (32'h1)
`endif
`ifndef SHA512_ACC_CSR_LOCK
`define SHA512_ACC_CSR_LOCK                                                                         (32'h0)
`define SHA512_ACC_CSR_LOCK_LOCK_LOW                                                                (0)
`define SHA512_ACC_CSR_LOCK_LOCK_MASK                                                               (32'h1)
`endif
`ifndef SHA512_ACC_CSR_USER
`define SHA512_ACC_CSR_USER                                                                         (32'h4)
`endif
`ifndef SHA512_ACC_CSR_MODE
`define SHA512_ACC_CSR_MODE                                                                         (32'h8)
`define SHA512_ACC_CSR_MODE_MODE_LOW                                                                (0)
`define SHA512_ACC_CSR_MODE_MODE_MASK                                                               (32'h3)
`define SHA512_ACC_CSR_MODE_ENDIAN_TOGGLE_LOW                                                       (2)
`define SHA512_ACC_CSR_MODE_ENDIAN_TOGGLE_MASK                                                      (32'h4)
`endif
`ifndef SHA512_ACC_CSR_START_ADDRESS
`define SHA512_ACC_CSR_START_ADDRESS                                                                (32'hc)
`endif
`ifndef SHA512_ACC_CSR_DLEN
`define SHA512_ACC_CSR_DLEN                                                                         (32'h10)
`endif
`ifndef SHA512_ACC_CSR_DATAIN
`define SHA512_ACC_CSR_DATAIN                                                                       (32'h14)
`endif
`ifndef SHA512_ACC_CSR_EXECUTE
`define SHA512_ACC_CSR_EXECUTE                                                                      (32'h18)
`define SHA512_ACC_CSR_EXECUTE_EXECUTE_LOW                                                          (0)
`define SHA512_ACC_CSR_EXECUTE_EXECUTE_MASK                                                         (32'h1)
`endif
`ifndef SHA512_ACC_CSR_STATUS
`define SHA512_ACC_CSR_STATUS                                                                       (32'h1c)
`define SHA512_ACC_CSR_STATUS_VALID_LOW                                                             (0)
`define SHA512_ACC_CSR_STATUS_VALID_MASK                                                            (32'h1)
`define SHA512_ACC_CSR_STATUS_SOC_HAS_LOCK_LOW                                                      (1)
`define SHA512_ACC_CSR_STATUS_SOC_HAS_LOCK_MASK                                                     (32'h2)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_0
`define SHA512_ACC_CSR_DIGEST_0                                                                     (32'h20)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_1
`define SHA512_ACC_CSR_DIGEST_1                                                                     (32'h24)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_2
`define SHA512_ACC_CSR_DIGEST_2                                                                     (32'h28)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_3
`define SHA512_ACC_CSR_DIGEST_3                                                                     (32'h2c)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_4
`define SHA512_ACC_CSR_DIGEST_4                                                                     (32'h30)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_5
`define SHA512_ACC_CSR_DIGEST_5                                                                     (32'h34)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_6
`define SHA512_ACC_CSR_DIGEST_6                                                                     (32'h38)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_7
`define SHA512_ACC_CSR_DIGEST_7                                                                     (32'h3c)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_8
`define SHA512_ACC_CSR_DIGEST_8                                                                     (32'h40)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_9
`define SHA512_ACC_CSR_DIGEST_9                                                                     (32'h44)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_10
`define SHA512_ACC_CSR_DIGEST_10                                                                    (32'h48)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_11
`define SHA512_ACC_CSR_DIGEST_11                                                                    (32'h4c)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_12
`define SHA512_ACC_CSR_DIGEST_12                                                                    (32'h50)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_13
`define SHA512_ACC_CSR_DIGEST_13                                                                    (32'h54)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_14
`define SHA512_ACC_CSR_DIGEST_14                                                                    (32'h58)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_15
`define SHA512_ACC_CSR_DIGEST_15                                                                    (32'h5c)
`endif
`ifndef SHA512_ACC_CSR_CONTROL
`define SHA512_ACC_CSR_CONTROL                                                                      (32'h60)
`define SHA512_ACC_CSR_CONTROL_ZEROIZE_LOW                                                          (0)
`define SHA512_ACC_CSR_CONTROL_ZEROIZE_MASK                                                         (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                               (32'h800)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                  (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                 (32'h1)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                  (1)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                 (32'h2)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                (32'h804)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_LOW                                  (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_MASK                                 (32'h1)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_LOW                                  (1)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_MASK                                 (32'h2)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_LOW                                  (2)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_MASK                                 (32'h4)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_LOW                                  (3)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_MASK                                 (32'h8)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_EN_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                (32'h808)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                          (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                         (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                            (32'h80c)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                               (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                            (32'h810)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                               (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                          (32'h814)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_LOW                           (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_MASK                          (32'h1)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_LOW                           (1)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_MASK                          (32'h2)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_LOW                           (2)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_MASK                          (32'h4)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_LOW                           (3)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK                          (32'h8)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                          (32'h818)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                   (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                  (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                              (32'h81c)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_LOW                              (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_MASK                             (32'h1)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_LOW                              (1)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_MASK                             (32'h2)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_LOW                              (2)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_MASK                             (32'h4)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_LOW                              (3)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_MASK                             (32'h8)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                              (32'h820)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                      (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                     (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R                                            (32'h900)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                            (32'h904)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                            (32'h908)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                            (32'h90c)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                    (32'h980)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R                                       (32'ha00)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_LOW                             (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_MASK                            (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                       (32'ha04)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_LOW                             (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_MASK                            (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                       (32'ha08)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_LOW                             (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_MASK                            (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                       (32'ha0c)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_LOW                             (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_MASK                            (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                               (32'ha10)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                     (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                    (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_HW_ERROR_FATAL
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL                                                            (32'h0)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_ICCM_ECC_UNC_LOW                                           (0)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_ICCM_ECC_UNC_MASK                                          (32'h1)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_DCCM_ECC_UNC_LOW                                           (1)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_DCCM_ECC_UNC_MASK                                          (32'h2)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_LOW                                                (2)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_MASK                                               (32'h4)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_CRYPTO_ERR_LOW                                             (3)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_CRYPTO_ERR_MASK                                            (32'h8)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_RSVD_LOW                                                   (4)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_RSVD_MASK                                                  (32'hfffffff0)
`endif
`ifndef SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL                                                        (32'h4)
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_NO_LOCK_LOW                                  (0)
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_NO_LOCK_MASK                                 (32'h1)
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_OOO_LOW                                      (1)
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_OOO_MASK                                     (32'h2)
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_ECC_UNC_LOW                                       (2)
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_ECC_UNC_MASK                                      (32'h4)
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_RSVD_LOW                                               (3)
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_RSVD_MASK                                              (32'hfffffff8)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_ERROR_FATAL
`define SOC_IFC_REG_CPTRA_FW_ERROR_FATAL                                                            (32'h8)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_ERROR_NON_FATAL
`define SOC_IFC_REG_CPTRA_FW_ERROR_NON_FATAL                                                        (32'hc)
`endif
`ifndef SOC_IFC_REG_CPTRA_HW_ERROR_ENC
`define SOC_IFC_REG_CPTRA_HW_ERROR_ENC                                                              (32'h10)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_ERROR_ENC
`define SOC_IFC_REG_CPTRA_FW_ERROR_ENC                                                              (32'h14)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0
`define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0                                                  (32'h18)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_1
`define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_1                                                  (32'h1c)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_2
`define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_2                                                  (32'h20)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_3
`define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_3                                                  (32'h24)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_4
`define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_4                                                  (32'h28)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_5
`define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_5                                                  (32'h2c)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_6
`define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_6                                                  (32'h30)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_7
`define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_7                                                  (32'h34)
`endif
`ifndef SOC_IFC_REG_CPTRA_BOOT_STATUS
`define SOC_IFC_REG_CPTRA_BOOT_STATUS                                                               (32'h38)
`endif
`ifndef SOC_IFC_REG_CPTRA_FLOW_STATUS
`define SOC_IFC_REG_CPTRA_FLOW_STATUS                                                               (32'h3c)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_STATUS_LOW                                                    (0)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_STATUS_MASK                                                   (32'hffffff)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_IDEVID_CSR_READY_LOW                                          (24)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_IDEVID_CSR_READY_MASK                                         (32'h1000000)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW                                               (25)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK                                              (32'he000000)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_LOW                                   (28)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK                                  (32'h10000000)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_LOW                                         (29)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_MASK                                        (32'h20000000)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_LOW                                           (30)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK                                          (32'h40000000)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_MAILBOX_FLOW_DONE_LOW                                         (31)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_MAILBOX_FLOW_DONE_MASK                                        (32'h80000000)
`endif
`ifndef SOC_IFC_REG_CPTRA_RESET_REASON
`define SOC_IFC_REG_CPTRA_RESET_REASON                                                              (32'h40)
`define SOC_IFC_REG_CPTRA_RESET_REASON_FW_UPD_RESET_LOW                                             (0)
`define SOC_IFC_REG_CPTRA_RESET_REASON_FW_UPD_RESET_MASK                                            (32'h1)
`define SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_LOW                                               (1)
`define SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK                                              (32'h2)
`endif
`ifndef SOC_IFC_REG_CPTRA_SECURITY_STATE
`define SOC_IFC_REG_CPTRA_SECURITY_STATE                                                            (32'h44)
`define SOC_IFC_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_LOW                                       (0)
`define SOC_IFC_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_MASK                                      (32'h3)
`define SOC_IFC_REG_CPTRA_SECURITY_STATE_DEBUG_LOCKED_LOW                                           (2)
`define SOC_IFC_REG_CPTRA_SECURITY_STATE_DEBUG_LOCKED_MASK                                          (32'h4)
`define SOC_IFC_REG_CPTRA_SECURITY_STATE_SCAN_MODE_LOW                                              (3)
`define SOC_IFC_REG_CPTRA_SECURITY_STATE_SCAN_MODE_MASK                                             (32'h8)
`define SOC_IFC_REG_CPTRA_SECURITY_STATE_RSVD_LOW                                                   (4)
`define SOC_IFC_REG_CPTRA_SECURITY_STATE_RSVD_MASK                                                  (32'hfffffff0)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0
`define SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0                                                     (32'h48)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_1
`define SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_1                                                     (32'h4c)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_2
`define SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_2                                                     (32'h50)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_3
`define SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_3                                                     (32'h54)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_4
`define SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_4                                                     (32'h58)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0                                                      (32'h5c)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_LOW                                             (0)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_MASK                                            (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1                                                      (32'h60)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1_LOCK_LOW                                             (0)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1_LOCK_MASK                                            (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2                                                      (32'h64)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2_LOCK_LOW                                             (0)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2_LOCK_MASK                                            (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3                                                      (32'h68)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3_LOCK_LOW                                             (0)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3_LOCK_MASK                                            (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4                                                      (32'h6c)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4_LOCK_LOW                                             (0)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4_LOCK_MASK                                            (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_VALID_AXI_USER
`define SOC_IFC_REG_CPTRA_TRNG_VALID_AXI_USER                                                       (32'h70)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK
`define SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK                                                        (32'h74)
`define SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK_LOCK_LOW                                               (0)
`define SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK_LOCK_MASK                                              (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_0
`define SOC_IFC_REG_CPTRA_TRNG_DATA_0                                                               (32'h78)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_1
`define SOC_IFC_REG_CPTRA_TRNG_DATA_1                                                               (32'h7c)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_2
`define SOC_IFC_REG_CPTRA_TRNG_DATA_2                                                               (32'h80)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_3
`define SOC_IFC_REG_CPTRA_TRNG_DATA_3                                                               (32'h84)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_4
`define SOC_IFC_REG_CPTRA_TRNG_DATA_4                                                               (32'h88)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_5
`define SOC_IFC_REG_CPTRA_TRNG_DATA_5                                                               (32'h8c)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_6
`define SOC_IFC_REG_CPTRA_TRNG_DATA_6                                                               (32'h90)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_7
`define SOC_IFC_REG_CPTRA_TRNG_DATA_7                                                               (32'h94)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_8
`define SOC_IFC_REG_CPTRA_TRNG_DATA_8                                                               (32'h98)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_9
`define SOC_IFC_REG_CPTRA_TRNG_DATA_9                                                               (32'h9c)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_10
`define SOC_IFC_REG_CPTRA_TRNG_DATA_10                                                              (32'ha0)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_11
`define SOC_IFC_REG_CPTRA_TRNG_DATA_11                                                              (32'ha4)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_CTRL
`define SOC_IFC_REG_CPTRA_TRNG_CTRL                                                                 (32'ha8)
`define SOC_IFC_REG_CPTRA_TRNG_CTRL_CLEAR_LOW                                                       (0)
`define SOC_IFC_REG_CPTRA_TRNG_CTRL_CLEAR_MASK                                                      (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_STATUS
`define SOC_IFC_REG_CPTRA_TRNG_STATUS                                                               (32'hac)
`define SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_REQ_LOW                                                  (0)
`define SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_REQ_MASK                                                 (32'h1)
`define SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_WR_DONE_LOW                                              (1)
`define SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_WR_DONE_MASK                                             (32'h2)
`endif
`ifndef SOC_IFC_REG_CPTRA_FUSE_WR_DONE
`define SOC_IFC_REG_CPTRA_FUSE_WR_DONE                                                              (32'hb0)
`define SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_LOW                                                     (0)
`define SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK                                                    (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_TIMER_CONFIG
`define SOC_IFC_REG_CPTRA_TIMER_CONFIG                                                              (32'hb4)
`endif
`ifndef SOC_IFC_REG_CPTRA_BOOTFSM_GO
`define SOC_IFC_REG_CPTRA_BOOTFSM_GO                                                                (32'hb8)
`define SOC_IFC_REG_CPTRA_BOOTFSM_GO_GO_LOW                                                         (0)
`define SOC_IFC_REG_CPTRA_BOOTFSM_GO_GO_MASK                                                        (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_DBG_MANUF_SERVICE_REG
`define SOC_IFC_REG_CPTRA_DBG_MANUF_SERVICE_REG                                                     (32'hbc)
`endif
`ifndef SOC_IFC_REG_CPTRA_CLK_GATING_EN
`define SOC_IFC_REG_CPTRA_CLK_GATING_EN                                                             (32'hc0)
`define SOC_IFC_REG_CPTRA_CLK_GATING_EN_CLK_GATING_EN_LOW                                           (0)
`define SOC_IFC_REG_CPTRA_CLK_GATING_EN_CLK_GATING_EN_MASK                                          (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0
`define SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0                                                     (32'hc4)
`endif
`ifndef SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_1
`define SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_1                                                     (32'hc8)
`endif
`ifndef SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0
`define SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0                                                    (32'hcc)
`endif
`ifndef SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1
`define SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1                                                    (32'hd0)
`endif
`ifndef SOC_IFC_REG_CPTRA_HW_REV_ID
`define SOC_IFC_REG_CPTRA_HW_REV_ID                                                                 (32'hd4)
`define SOC_IFC_REG_CPTRA_HW_REV_ID_CPTRA_GENERATION_LOW                                            (0)
`define SOC_IFC_REG_CPTRA_HW_REV_ID_CPTRA_GENERATION_MASK                                           (32'hffff)
`define SOC_IFC_REG_CPTRA_HW_REV_ID_SOC_STEPPING_ID_LOW                                             (16)
`define SOC_IFC_REG_CPTRA_HW_REV_ID_SOC_STEPPING_ID_MASK                                            (32'hffff0000)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_REV_ID_0
`define SOC_IFC_REG_CPTRA_FW_REV_ID_0                                                               (32'hd8)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_REV_ID_1
`define SOC_IFC_REG_CPTRA_FW_REV_ID_1                                                               (32'hdc)
`endif
`ifndef SOC_IFC_REG_CPTRA_HW_CONFIG
`define SOC_IFC_REG_CPTRA_HW_CONFIG                                                                 (32'he0)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_LOW                                                    (0)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK                                                   (32'h1)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_RSVD_EN_LOW                                                     (1)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_RSVD_EN_MASK                                                    (32'he)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_LMS_ACC_EN_LOW                                                  (4)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_LMS_ACC_EN_MASK                                                 (32'h10)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_LOW                                           (5)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_MASK                                          (32'h20)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_TIMER1_EN
`define SOC_IFC_REG_CPTRA_WDT_TIMER1_EN                                                             (32'he4)
`define SOC_IFC_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_LOW                                               (0)
`define SOC_IFC_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_MASK                                              (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL
`define SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL                                                           (32'he8)
`define SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_LOW                                        (0)
`define SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK                                       (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0
`define SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0                                               (32'hec)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1
`define SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1                                               (32'hf0)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_TIMER2_EN
`define SOC_IFC_REG_CPTRA_WDT_TIMER2_EN                                                             (32'hf4)
`define SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_LOW                                               (0)
`define SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_MASK                                              (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL
`define SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL                                                           (32'hf8)
`define SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART_LOW                                        (0)
`define SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART_MASK                                       (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0
`define SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0                                               (32'hfc)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1
`define SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1                                               (32'h100)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_STATUS
`define SOC_IFC_REG_CPTRA_WDT_STATUS                                                                (32'h104)
`define SOC_IFC_REG_CPTRA_WDT_STATUS_T1_TIMEOUT_LOW                                                 (0)
`define SOC_IFC_REG_CPTRA_WDT_STATUS_T1_TIMEOUT_MASK                                                (32'h1)
`define SOC_IFC_REG_CPTRA_WDT_STATUS_T2_TIMEOUT_LOW                                                 (1)
`define SOC_IFC_REG_CPTRA_WDT_STATUS_T2_TIMEOUT_MASK                                                (32'h2)
`endif
`ifndef SOC_IFC_REG_CPTRA_FUSE_VALID_AXI_USER
`define SOC_IFC_REG_CPTRA_FUSE_VALID_AXI_USER                                                       (32'h108)
`endif
`ifndef SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK
`define SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK                                                        (32'h10c)
`define SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK_LOCK_LOW                                               (0)
`define SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK_LOCK_MASK                                              (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_CFG_0
`define SOC_IFC_REG_CPTRA_WDT_CFG_0                                                                 (32'h110)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_CFG_1
`define SOC_IFC_REG_CPTRA_WDT_CFG_1                                                                 (32'h114)
`endif
`ifndef SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0                                                    (32'h118)
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_LOW_THRESHOLD_LOW                                  (0)
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_LOW_THRESHOLD_MASK                                 (32'hffff)
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_HIGH_THRESHOLD_LOW                                 (16)
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_HIGH_THRESHOLD_MASK                                (32'hffff0000)
`endif
`ifndef SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1                                                    (32'h11c)
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_REPETITION_COUNT_LOW                               (0)
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_REPETITION_COUNT_MASK                              (32'hffff)
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_RSVD_LOW                                           (16)
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_RSVD_MASK                                          (32'hffff0000)
`endif
`ifndef SOC_IFC_REG_CPTRA_RSVD_REG_0
`define SOC_IFC_REG_CPTRA_RSVD_REG_0                                                                (32'h120)
`endif
`ifndef SOC_IFC_REG_CPTRA_RSVD_REG_1
`define SOC_IFC_REG_CPTRA_RSVD_REG_1                                                                (32'h124)
`endif
`ifndef SOC_IFC_REG_CPTRA_HW_CAPABILITIES
`define SOC_IFC_REG_CPTRA_HW_CAPABILITIES                                                           (32'h128)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_CAPABILITIES
`define SOC_IFC_REG_CPTRA_FW_CAPABILITIES                                                           (32'h12c)
`endif
`ifndef SOC_IFC_REG_CPTRA_CAP_LOCK
`define SOC_IFC_REG_CPTRA_CAP_LOCK                                                                  (32'h130)
`define SOC_IFC_REG_CPTRA_CAP_LOCK_LOCK_LOW                                                         (0)
`define SOC_IFC_REG_CPTRA_CAP_LOCK_LOCK_MASK                                                        (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_0
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_0                                                           (32'h140)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_1
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_1                                                           (32'h144)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_2
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_2                                                           (32'h148)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_3
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_3                                                           (32'h14c)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_4
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_4                                                           (32'h150)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_5
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_5                                                           (32'h154)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_6
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_6                                                           (32'h158)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_7
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_7                                                           (32'h15c)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_8
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_8                                                           (32'h160)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_9
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_9                                                           (32'h164)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_10
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_10                                                          (32'h168)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_11
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_11                                                          (32'h16c)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK                                                        (32'h170)
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK_LOCK_LOW                                               (0)
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK_LOCK_MASK                                              (32'h1)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_0
`define SOC_IFC_REG_FUSE_UDS_SEED_0                                                                 (32'h200)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_1
`define SOC_IFC_REG_FUSE_UDS_SEED_1                                                                 (32'h204)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_2
`define SOC_IFC_REG_FUSE_UDS_SEED_2                                                                 (32'h208)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_3
`define SOC_IFC_REG_FUSE_UDS_SEED_3                                                                 (32'h20c)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_4
`define SOC_IFC_REG_FUSE_UDS_SEED_4                                                                 (32'h210)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_5
`define SOC_IFC_REG_FUSE_UDS_SEED_5                                                                 (32'h214)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_6
`define SOC_IFC_REG_FUSE_UDS_SEED_6                                                                 (32'h218)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_7
`define SOC_IFC_REG_FUSE_UDS_SEED_7                                                                 (32'h21c)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_8
`define SOC_IFC_REG_FUSE_UDS_SEED_8                                                                 (32'h220)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_9
`define SOC_IFC_REG_FUSE_UDS_SEED_9                                                                 (32'h224)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_10
`define SOC_IFC_REG_FUSE_UDS_SEED_10                                                                (32'h228)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_11
`define SOC_IFC_REG_FUSE_UDS_SEED_11                                                                (32'h22c)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_12
`define SOC_IFC_REG_FUSE_UDS_SEED_12                                                                (32'h230)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_13
`define SOC_IFC_REG_FUSE_UDS_SEED_13                                                                (32'h234)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_14
`define SOC_IFC_REG_FUSE_UDS_SEED_14                                                                (32'h238)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_15
`define SOC_IFC_REG_FUSE_UDS_SEED_15                                                                (32'h23c)
`endif
`ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_0
`define SOC_IFC_REG_FUSE_FIELD_ENTROPY_0                                                            (32'h240)
`endif
`ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_1
`define SOC_IFC_REG_FUSE_FIELD_ENTROPY_1                                                            (32'h244)
`endif
`ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_2
`define SOC_IFC_REG_FUSE_FIELD_ENTROPY_2                                                            (32'h248)
`endif
`ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_3
`define SOC_IFC_REG_FUSE_FIELD_ENTROPY_3                                                            (32'h24c)
`endif
`ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_4
`define SOC_IFC_REG_FUSE_FIELD_ENTROPY_4                                                            (32'h250)
`endif
`ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_5
`define SOC_IFC_REG_FUSE_FIELD_ENTROPY_5                                                            (32'h254)
`endif
`ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_6
`define SOC_IFC_REG_FUSE_FIELD_ENTROPY_6                                                            (32'h258)
`endif
`ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_7
`define SOC_IFC_REG_FUSE_FIELD_ENTROPY_7                                                            (32'h25c)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_0
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_0                                                           (32'h260)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_1
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_1                                                           (32'h264)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_2
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_2                                                           (32'h268)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_3
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_3                                                           (32'h26c)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_4
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_4                                                           (32'h270)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_5
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_5                                                           (32'h274)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_6
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_6                                                           (32'h278)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_7
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_7                                                           (32'h27c)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_8
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_8                                                           (32'h280)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_9
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_9                                                           (32'h284)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_10
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_10                                                          (32'h288)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_11
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_11                                                          (32'h28c)
`endif
`ifndef SOC_IFC_REG_FUSE_ECC_REVOCATION
`define SOC_IFC_REG_FUSE_ECC_REVOCATION                                                             (32'h290)
`define SOC_IFC_REG_FUSE_ECC_REVOCATION_ECC_REVOCATION_LOW                                          (0)
`define SOC_IFC_REG_FUSE_ECC_REVOCATION_ECC_REVOCATION_MASK                                         (32'hf)
`endif
`ifndef SOC_IFC_REG_FUSE_FMC_KEY_MANIFEST_SVN
`define SOC_IFC_REG_FUSE_FMC_KEY_MANIFEST_SVN                                                       (32'h2b4)
`endif
`ifndef SOC_IFC_REG_FUSE_RUNTIME_SVN_0
`define SOC_IFC_REG_FUSE_RUNTIME_SVN_0                                                              (32'h2b8)
`endif
`ifndef SOC_IFC_REG_FUSE_RUNTIME_SVN_1
`define SOC_IFC_REG_FUSE_RUNTIME_SVN_1                                                              (32'h2bc)
`endif
`ifndef SOC_IFC_REG_FUSE_RUNTIME_SVN_2
`define SOC_IFC_REG_FUSE_RUNTIME_SVN_2                                                              (32'h2c0)
`endif
`ifndef SOC_IFC_REG_FUSE_RUNTIME_SVN_3
`define SOC_IFC_REG_FUSE_RUNTIME_SVN_3                                                              (32'h2c4)
`endif
`ifndef SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE
`define SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE                                                      (32'h2c8)
`define SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE_DIS_LOW                                              (0)
`define SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE_DIS_MASK                                             (32'h1)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0                                                         (32'h2cc)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_1
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_1                                                         (32'h2d0)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_2
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_2                                                         (32'h2d4)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_3
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_3                                                         (32'h2d8)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_4
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_4                                                         (32'h2dc)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_5
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_5                                                         (32'h2e0)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_6
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_6                                                         (32'h2e4)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_7
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_7                                                         (32'h2e8)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_8
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_8                                                         (32'h2ec)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_9
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_9                                                         (32'h2f0)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_10
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_10                                                        (32'h2f4)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_11
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_11                                                        (32'h2f8)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_12
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_12                                                        (32'h2fc)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_13
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_13                                                        (32'h300)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_14
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_14                                                        (32'h304)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_15
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_15                                                        (32'h308)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_16
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_16                                                        (32'h30c)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_17
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_17                                                        (32'h310)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_18
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_18                                                        (32'h314)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_19
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_19                                                        (32'h318)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_20
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_20                                                        (32'h31c)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_21
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_21                                                        (32'h320)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_22
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_22                                                        (32'h324)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_23
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_23                                                        (32'h328)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_0
`define SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_0                                                      (32'h32c)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_1
`define SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_1                                                      (32'h330)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_2
`define SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_2                                                      (32'h334)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_3
`define SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_3                                                      (32'h338)
`endif
`ifndef SOC_IFC_REG_FUSE_LMS_REVOCATION
`define SOC_IFC_REG_FUSE_LMS_REVOCATION                                                             (32'h340)
`endif
`ifndef SOC_IFC_REG_FUSE_MLDSA_REVOCATION
`define SOC_IFC_REG_FUSE_MLDSA_REVOCATION                                                           (32'h344)
`define SOC_IFC_REG_FUSE_MLDSA_REVOCATION_MLDSA_REVOCATION_LOW                                      (0)
`define SOC_IFC_REG_FUSE_MLDSA_REVOCATION_MLDSA_REVOCATION_MASK                                     (32'hf)
`endif
`ifndef SOC_IFC_REG_FUSE_SOC_STEPPING_ID
`define SOC_IFC_REG_FUSE_SOC_STEPPING_ID                                                            (32'h348)
`define SOC_IFC_REG_FUSE_SOC_STEPPING_ID_SOC_STEPPING_ID_LOW                                        (0)
`define SOC_IFC_REG_FUSE_SOC_STEPPING_ID_SOC_STEPPING_ID_MASK                                       (32'hffff)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0                                                   (32'h34c)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_1
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_1                                                   (32'h350)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_2
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_2                                                   (32'h354)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_3
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_3                                                   (32'h358)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_4
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_4                                                   (32'h35c)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_5
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_5                                                   (32'h360)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_6
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_6                                                   (32'h364)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_7
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_7                                                   (32'h368)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_8
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_8                                                   (32'h36c)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_9
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_9                                                   (32'h370)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_10
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_10                                                  (32'h374)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_11
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_11                                                  (32'h378)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_12
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_12                                                  (32'h37c)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_13
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_13                                                  (32'h380)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_14
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_14                                                  (32'h384)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_15
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_15                                                  (32'h388)
`endif
`ifndef SOC_IFC_REG_FUSE_PQC_KEY_TYPE
`define SOC_IFC_REG_FUSE_PQC_KEY_TYPE                                                               (32'h38c)
`define SOC_IFC_REG_FUSE_PQC_KEY_TYPE_KEY_TYPE_LOW                                                  (0)
`define SOC_IFC_REG_FUSE_PQC_KEY_TYPE_KEY_TYPE_MASK                                                 (32'h3)
`endif
`ifndef SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_0
`define SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_0                                                         (32'h390)
`endif
`ifndef SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_1
`define SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_1                                                         (32'h394)
`endif
`ifndef SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_2
`define SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_2                                                         (32'h398)
`endif
`ifndef SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_3
`define SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_3                                                         (32'h39c)
`endif
`ifndef SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN
`define SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN                                                       (32'h3a0)
`define SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN_SVN_LOW                                               (0)
`define SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN_SVN_MASK                                              (32'hff)
`endif
`ifndef SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_L
`define SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_L                                                         (32'h500)
`endif
`ifndef SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_H
`define SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_H                                                         (32'h504)
`endif
`ifndef SOC_IFC_REG_SS_MCI_BASE_ADDR_L
`define SOC_IFC_REG_SS_MCI_BASE_ADDR_L                                                              (32'h508)
`endif
`ifndef SOC_IFC_REG_SS_MCI_BASE_ADDR_H
`define SOC_IFC_REG_SS_MCI_BASE_ADDR_H                                                              (32'h50c)
`endif
`ifndef SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_L
`define SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_L                                                     (32'h510)
`endif
`ifndef SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_H
`define SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_H                                                     (32'h514)
`endif
`ifndef SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_L
`define SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_L                                                           (32'h518)
`endif
`ifndef SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_H
`define SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_H                                                           (32'h51c)
`endif
`ifndef SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_L
`define SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_L                                                         (32'h520)
`endif
`ifndef SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_H
`define SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_H                                                         (32'h524)
`endif
`ifndef SOC_IFC_REG_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET
`define SOC_IFC_REG_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET                               (32'h528)
`endif
`ifndef SOC_IFC_REG_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES
`define SOC_IFC_REG_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES                                      (32'h52c)
`endif
`ifndef SOC_IFC_REG_SS_DEBUG_INTENT
`define SOC_IFC_REG_SS_DEBUG_INTENT                                                                 (32'h530)
`define SOC_IFC_REG_SS_DEBUG_INTENT_DEBUG_INTENT_LOW                                                (0)
`define SOC_IFC_REG_SS_DEBUG_INTENT_DEBUG_INTENT_MASK                                               (32'h1)
`endif
`ifndef SOC_IFC_REG_SS_CALIPTRA_DMA_AXI_USER
`define SOC_IFC_REG_SS_CALIPTRA_DMA_AXI_USER                                                        (32'h534)
`endif
`ifndef SOC_IFC_REG_SS_STRAP_GENERIC_0
`define SOC_IFC_REG_SS_STRAP_GENERIC_0                                                              (32'h5a0)
`endif
`ifndef SOC_IFC_REG_SS_STRAP_GENERIC_1
`define SOC_IFC_REG_SS_STRAP_GENERIC_1                                                              (32'h5a4)
`endif
`ifndef SOC_IFC_REG_SS_STRAP_GENERIC_2
`define SOC_IFC_REG_SS_STRAP_GENERIC_2                                                              (32'h5a8)
`endif
`ifndef SOC_IFC_REG_SS_STRAP_GENERIC_3
`define SOC_IFC_REG_SS_STRAP_GENERIC_3                                                              (32'h5ac)
`endif
`ifndef SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ                                                    (32'h5c0)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ_MANUF_DBG_UNLOCK_REQ_LOW                           (0)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ_MANUF_DBG_UNLOCK_REQ_MASK                          (32'h1)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ_PROD_DBG_UNLOCK_REQ_LOW                            (1)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ_PROD_DBG_UNLOCK_REQ_MASK                           (32'h2)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ_UDS_PROGRAM_REQ_LOW                                (2)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ_UDS_PROGRAM_REQ_MASK                               (32'h4)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ_RSVD_LOW                                           (3)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ_RSVD_MASK                                          (32'hfffffff8)
`endif
`ifndef SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP                                                    (32'h5c4)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_LOW                       (0)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_MASK                      (32'h1)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_FAIL_LOW                          (1)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_FAIL_MASK                         (32'h2)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_LOW                   (2)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_MASK                  (32'h4)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_LOW                        (3)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_MASK                       (32'h8)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_PROD_DBG_UNLOCK_FAIL_LOW                           (4)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_PROD_DBG_UNLOCK_FAIL_MASK                          (32'h10)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_PROD_DBG_UNLOCK_IN_PROGRESS_LOW                    (5)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_PROD_DBG_UNLOCK_IN_PROGRESS_MASK                   (32'h20)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_LOW                            (6)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK                           (32'h40)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_LOW                               (7)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_MASK                              (32'h80)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_LOW                        (8)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_MASK                       (32'h100)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_LOW                          (9)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_MASK                         (32'h200)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_RSVD_LOW                                           (10)
`define SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_RSVD_MASK                                          (32'hfffffc00)
`endif
`ifndef SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_0
`define SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_0                                                       (32'h5c8)
`endif
`ifndef SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_1
`define SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_1                                                       (32'h5cc)
`endif
`ifndef SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0
`define SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0                                                       (32'h5d0)
`endif
`ifndef SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_1
`define SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_1                                                       (32'h5d4)
`endif
`ifndef SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_2
`define SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_2                                                       (32'h5d8)
`endif
`ifndef SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_3
`define SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_3                                                       (32'h5dc)
`endif


`endif