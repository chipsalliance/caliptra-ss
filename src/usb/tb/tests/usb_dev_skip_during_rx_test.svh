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

// Runs endpoint skip while EP1 OUT packet processing is being requested.
class usb_dev_skip_during_rx_test extends usb_base_test;
  `uvm_component_utils(usb_dev_skip_during_rx_test)

  function new(string name = "usb_dev_skip_during_rx_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 3ms;
  endfunction

  task run_phase(uvm_phase phase);
    usb_dev_skip_during_rx_seq skip_sequence;

    phase.raise_objection(this);
    `uvm_info("USB_SKIP_RX_TEST", $sformatf("Starting endpoint skip-during-receive test; timeout=%0t", test_timeout), UVM_LOW)
    env.wait_for_reset();
    if (env.host_agent == null || env.host_agent.virt_sequencer == null) begin
      `uvm_fatal("USB_SKIP_RX_TEST", "The scenario requires an active SVT host agent")
    end

    skip_sequence = usb_dev_skip_during_rx_seq::type_id::create("skip_sequence");
    skip_sequence.start(env.virtual_sequencer);
    scenario_completed = skip_sequence.completed;
    `uvm_info("USB_SKIP_RX_TEST", "Skip-during-receive sequence returned; entering final UVM checks", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
