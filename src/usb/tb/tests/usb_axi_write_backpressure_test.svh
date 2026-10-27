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

// B-1 write-path probe: fills B FIFOs with overlapping writes. usb_top_tb's
// AHB HREADY checks flag any bridge-originated wait on the final write beat.
class usb_axi_write_backpressure_test extends usb_base_test;
  `uvm_component_utils(usb_axi_write_backpressure_test)

  function new(string name = "usb_axi_write_backpressure_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Use exact stimulus. The environment's outstanding depth already lets the
  // overlapping writes fill each bridge's two-entry B FIFO.
  virtual function void configure_env_cfg(usb_env_cfg cfg);
    cfg.axi_delay_random = 1'b0;
  endfunction

  task run_phase(uvm_phase phase);
    usb_axi_write_backpressure_seq seq;

    phase.raise_objection(this);
    env.wait_for_reset();
    seq = usb_axi_write_backpressure_seq::type_id::create("write_backpressure_sequence");
    seq.start(env.virtual_sequencer);
    scenario_completed = seq.completed;
    phase.drop_objection(this);
  endtask
endclass
