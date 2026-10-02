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

// B-1 prosecutor: the same immutable register must survive a full R FIFO.
// usb_axi_read_backpressure_seq issues the reads and checks every beat.
class usb_axi_read_backpressure_test extends usb_base_test;
  `uvm_component_utils(usb_axi_read_backpressure_test)

  function new(string name = "usb_axi_read_backpressure_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Default to exact stimulus; +usb_axi_delay_random can still override it.
  function void build_phase(uvm_phase phase);
    uvm_config_db#(bit)::set(this, "env", "axi_delay_random", 1'b0);
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    usb_axi_read_backpressure_seq seq;

    phase.raise_objection(this);
    env.wait_for_reset();
    seq = usb_axi_read_backpressure_seq::type_id::create("read_backpressure_sequence");
    seq.start(env.virtual_sequencer);
    scenario_completed = seq.completed;
    phase.drop_objection(this);
  endtask
endclass
