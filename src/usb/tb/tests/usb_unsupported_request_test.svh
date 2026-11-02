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

// Verifies unsupported EP0 requests terminate with a device STALL.
class usb_unsupported_request_test extends usb_base_test;
  `uvm_component_utils(usb_unsupported_request_test)

  function new(string name = "usb_unsupported_request_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 2ms;
  endfunction

  task run_phase(uvm_phase phase);
    usb_unsupported_request_seq request_sequence;

    phase.raise_objection(this);
    `uvm_info("USB_UNSUPPORTED_TEST", $sformatf("Starting unsupported-request STALL test; timeout=%0t", test_timeout), UVM_LOW)
    env.wait_for_reset();
    request_sequence = usb_unsupported_request_seq::type_id::create("request_sequence");
    request_sequence.start(env.virtual_sequencer);
    scenario_completed = request_sequence.completed;
    `uvm_info("USB_UNSUPPORTED_TEST", "Unsupported-request sequence returned; entering final UVM checks", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
