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
// Runs the standalone USB INIT scenario against the real compound USB DUT.
// It uses the Synopsys SVT host, starts usb_init_seq on the environment virtual
// sequencer, and reports success only after all seven control transfers and
// device-side EP0 operations complete.
class usb_init_test extends usb_base_test;
  `uvm_component_utils(usb_init_test)

  function new(string name = "usb_init_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function time selected_test_timeout();
    return USB_INIT_TEST_TIMEOUT;
  endfunction

  task run_phase(uvm_phase phase);
    usb_init_seq init_sequence;

    phase.raise_objection(this);
    `uvm_info("USB_INIT_TEST", $sformatf("Starting real-traffic USB INIT test; timeout=%0t", selected_test_timeout()), UVM_LOW)
    env.wait_for_reset();
    if (env.host_agent == null || env.host_agent.virt_sequencer == null) begin
      `uvm_fatal("USB_INIT_TEST", "USB INIT requires an active SVT host agent")
    end

    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(env.virtual_sequencer);
    scenario_completed = init_sequence.completed;
    `uvm_info("USB_INIT_TEST", "USB INIT sequence returned; entering final UVM checks", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
