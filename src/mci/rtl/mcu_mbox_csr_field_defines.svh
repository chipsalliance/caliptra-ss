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
`ifndef MCU_MBOX_CSR_FIELD_DEFINES_HEADER
`define MCU_MBOX_CSR_FIELD_DEFINES_HEADER


`ifndef MCU_MBOX_CSR_MBOX_LOCK
`define MCU_MBOX_CSR_MBOX_LOCK                                                                      (32'h200000)
`define MCU_MBOX_CSR_MBOX_LOCK_LOCK_LOW                                                             (0)
`define MCU_MBOX_CSR_MBOX_LOCK_LOCK_MASK                                                            (32'h1)
`endif
`ifndef MCU_MBOX_CSR_MBOX_USER
`define MCU_MBOX_CSR_MBOX_USER                                                                      (32'h200004)
`endif
`ifndef MCU_MBOX_CSR_MBOX_TARGET_USER
`define MCU_MBOX_CSR_MBOX_TARGET_USER                                                               (32'h200008)
`endif
`ifndef MCU_MBOX_CSR_MBOX_CMD
`define MCU_MBOX_CSR_MBOX_CMD                                                                       (32'h20000c)
`endif
`ifndef MCU_MBOX_CSR_MBOX_DLEN
`define MCU_MBOX_CSR_MBOX_DLEN                                                                      (32'h200010)
`endif
`ifndef MCU_MBOX_CSR_MBOX_EXECUTE
`define MCU_MBOX_CSR_MBOX_EXECUTE                                                                   (32'h200014)
`define MCU_MBOX_CSR_MBOX_EXECUTE_EXECUTE_LOW                                                       (0)
`define MCU_MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK                                                      (32'h1)
`endif


`endif