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
// Shared execution context for USB environment-level sequences.
class usb_virtual_sequencer extends uvm_sequencer #(uvm_sequence_item);
  `uvm_component_utils(usb_virtual_sequencer)

  usb_reg_model reg_model;
  // Supplies the endpoint configurations so sequences resolve endpoints by
  // protocol identity instead of embedding anchor or physical indices.
  usb_env_cfg cfg;
  aaxi_sequencer combo_sequencer;
  aaxi_sequencer dev0_memory_sequencer;
  aaxi_sequencer dev1_csr_sequencer;
  aaxi_sequencer dev1_memory_sequencer;
  svt_usb_virtual_sequencer host_sequencer;
  // usb_env creates/registers these callbacks; sequences use the same objects
  // through p_sequencer. Each window, queue, or expectation has one sequence
  // owner; concurrent sequences must not reset or consume another's state.
  // See each callback's class comments for its API and VIP documentation.
  usb_packet_monitor_callback packet_monitor;
  usb_vip_physical_monitor_callback physical_monitor;
  usb_vip_raw_rx_callback raw_rx;
  // AXI USER filter policy control shared by all four manager paths.
  virtual usb_tb_ctrl_if #(
    .UW(usb_tb_pkg::USB_TB_AXI_USER_WIDTH),
    .COMBO_NUM_USERS(usb_tb_pkg::USB_COMBO_NUM_PRIV_AXI_USERS),
    .DEV1_NUM_USERS(usb_tb_pkg::USB_DEV1_NUM_PRIV_AXI_USERS)
  ) ctrl_vif;

  function new(string name = "usb_virtual_sequencer", uvm_component parent = null);
    super.new(name, parent);
  endfunction
endclass
