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

// Runs double-buffer bulk USB traffic with concurrent checked DEV0 RAM and Combo (Hub) AXI accesses.
class usb_axi_during_usb_traffic_test extends usb_base_test;
  `uvm_component_utils(usb_axi_during_usb_traffic_test)

  function new(string name = "usb_axi_during_usb_traffic_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 5ms;
  endfunction

  task run_phase(uvm_phase phase);
    usb_axi_during_usb_traffic_seq seq;

    phase.raise_objection(this);
    `uvm_info("USB_TEST", $sformatf("Starting AXI-during-USB traffic test; timeout=%0t", test_timeout), UVM_LOW)
    env.wait_for_reset();
    seq = usb_axi_during_usb_traffic_seq::type_id::create("axi_during_usb_sequence");
    seq.start(env.virtual_sequencer);
    scenario_completed = seq.completed;
    phase.drop_objection(this);
  endtask
endclass
