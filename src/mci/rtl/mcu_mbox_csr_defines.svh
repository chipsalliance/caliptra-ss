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
`ifndef MCU_MBOX_CSR_DEFINES_HEADER
`define MCU_MBOX_CSR_DEFINES_HEADER


`define MCU_MBOX_CSR_BASE_ADDR                                                                      (32'h0)
`define MCU_MBOX_CSR_MBOX_SRAM_BASE_ADDR                                                            (32'h0)
`define MCU_MBOX_CSR_MBOX_SRAM_END_ADDR                                                             (32'h1fffff)
`define MCU_MBOX_CSR_MBOX_LOCK                                                                      (32'h200000)
`define MCU_MBOX_CSR_MBOX_USER                                                                      (32'h200004)
`define MCU_MBOX_CSR_MBOX_TARGET_USER                                                               (32'h200008)
`define MCU_MBOX_CSR_MBOX_TARGET_USER_VALID                                                         (32'h20000c)
`define MCU_MBOX_CSR_MBOX_CMD                                                                       (32'h200010)
`define MCU_MBOX_CSR_MBOX_DLEN                                                                      (32'h200014)
`define MCU_MBOX_CSR_MBOX_EXECUTE                                                                   (32'h200018)
`define MCU_MBOX_CSR_MBOX_TARGET_STATUS                                                             (32'h20001c)
`define MCU_MBOX_CSR_MBOX_CMD_STATUS                                                                (32'h200020)
`define MCU_MBOX_CSR_MBOX_HW_STATUS                                                                 (32'h200024)


`endif