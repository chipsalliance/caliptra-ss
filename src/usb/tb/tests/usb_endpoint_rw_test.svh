// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// you may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// Runs the standalone five-target AXI smoke without USB protocol traffic.
// The test starts usb_endpoint_rw_seq on the environment virtual sequencer and
// reports success only after every response, data, preservation, isolation,
// restoration, and completion-count check has passed.
class usb_endpoint_rw_test extends usb_base_test;
  `uvm_component_utils(usb_endpoint_rw_test)

  function new(string name = "usb_endpoint_rw_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    usb_endpoint_rw_seq seq;
    phase.raise_objection(this);
    `uvm_info("USB_TEST", $sformatf("Starting endpoint read/write test; whole-test timeout=%0t", USB_TEST_TIMEOUT), UVM_LOW)
    env.wait_for_reset();
    seq = usb_endpoint_rw_seq::type_id::create("endpoint_rw_sequence");
    seq.start(env.virtual_sequencer);
    scenario_completed = seq.completed;
    `uvm_info("USB_TEST", "Endpoint sequence returned; entering UVM final checks", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
