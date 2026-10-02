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

// Randomized AXI outstanding-transaction stress on all four USB AXI ports.
// Keeps the environment's randomized AXI delays and starts no USB traffic.
class usb_axi_stress_test extends usb_base_test;
  `uvm_component_utils(usb_axi_stress_test)

  // Full 64 KiB fill and sweep of both SRAMs plus the stress phase.
  localparam time STRESS_TEST_TIMEOUT = 5ms;

  function new(string name = "usb_axi_stress_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function time selected_test_timeout();
    return STRESS_TEST_TIMEOUT;
  endfunction

  task run_phase(uvm_phase phase);
    usb_axi_stress_seq seq;

    phase.raise_objection(this);
    env.wait_for_reset();
    seq = usb_axi_stress_seq::type_id::create("axi_stress_sequence");
    seq.start(env.virtual_sequencer);
    scenario_completed = seq.completed;
    phase.drop_objection(this);
  endtask
endclass
