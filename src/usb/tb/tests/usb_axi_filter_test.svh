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
// Runs the directed four-path AXI USER filter evaluation without USB protocol
// traffic. The test starts usb_axi_filter_seq on the environment virtual
// sequencer and reports success only after every allow, deny, preservation,
// recovery, rejected-burst, accepted-burst, restore, and completion-count check
// has passed.
class usb_axi_filter_test extends usb_base_test;
  `uvm_component_utils(usb_axi_filter_test)

  // Register the test under its parent; usb_base_test builds the environment.
  function new(string name = "usb_axi_filter_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Wait for reset, run usb_axi_filter_seq on the virtual sequencer, and hand
  // its completed flag to usb_base_test for the final pass/fail report.
  task run_phase(uvm_phase phase);
    usb_axi_filter_seq seq;
    phase.raise_objection(this);
    `uvm_info("USB_TEST", $sformatf("Starting AXI USER filter test; whole-test timeout=%0t", USB_TEST_TIMEOUT), UVM_LOW)
    env.wait_for_reset();
    seq = usb_axi_filter_seq::type_id::create("axi_filter_sequence");
    seq.start(env.virtual_sequencer);
    scenario_completed = seq.completed;
    `uvm_info("USB_TEST", "AXI USER filter sequence returned; entering UVM final checks", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
