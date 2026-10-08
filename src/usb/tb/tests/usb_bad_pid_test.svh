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

// Verifies PID complement checking and subsequent traffic recovery.
class usb_bad_pid_test extends usb_base_test;
  `uvm_component_utils(usb_bad_pid_test)

  function new(string name = "usb_bad_pid_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 3ms;
  endfunction

  task run_phase(uvm_phase phase);
    usb_bad_pid_seq pid_sequence;

    phase.raise_objection(this);
    `uvm_info("USB_BAD_PID_TEST", $sformatf("Starting bad PID encoding test; timeout=%0t", test_timeout), UVM_LOW)
    env.wait_for_reset();
    pid_sequence = usb_bad_pid_seq::type_id::create("pid_sequence");
    pid_sequence.start(env.virtual_sequencer);
    scenario_completed = pid_sequence.completed;
    `uvm_info("USB_BAD_PID_TEST", "Bad PID sequence returned; entering final UVM checks", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
