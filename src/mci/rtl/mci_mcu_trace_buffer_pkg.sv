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

package mci_mcu_trace_buffer_pkg;

  typedef struct packed {
    logic [24:0] reserved; 
    logic        trace_rv_i_interrupt_ip;
    logic [ 4:0] trace_rv_i_ecause_ip;
    logic        trace_rv_i_exception_ip;
    logic [31:0] trace_rv_i_tval_ip;
    logic [31:0] trace_rv_i_address_ip;
    logic [31:0] trace_rv_i_insn_ip;
  } mci_mcu_trace_packet_t;

  typedef struct packed {
    logic [31:0] TRACE_STATUS;
    logic [31:0] TRACE_CONFIG;
    logic [31:0] TRACE_WR_PTR;
    logic [31:0] TRACE_RD_PTR;
    logic [31:0] TRACE_DATA; 
  } mci_mcu_trace_buffer_dmi_reg_t;

  // Add 31 to round up in case the packet is not a multiple of 32.
  parameter MCI_MCU_TRACE_PACKET_NUM_DWORDS = ($bits(mci_mcu_trace_packet_t)  + 31)/ 32;

endpackage