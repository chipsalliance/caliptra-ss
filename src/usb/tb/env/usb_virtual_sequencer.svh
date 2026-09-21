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
  aaxi_sequencer combo_sequencer;
  aaxi_sequencer dev0_memory_sequencer;
  aaxi_sequencer dev1_csr_sequencer;
  aaxi_sequencer dev1_memory_sequencer;
  svt_usb_virtual_sequencer host_sequencer;

  function new(string name = "usb_virtual_sequencer", uvm_component parent = null);
    super.new(name, parent);
  endfunction
endclass
