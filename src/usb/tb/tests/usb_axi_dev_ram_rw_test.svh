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
class usb_axi_dev_ram_rw_test extends usb_base_test;
  `uvm_component_utils(usb_axi_dev_ram_rw_test)

  function new(string name = "usb_axi_dev_ram_rw_test", uvm_component parent = null);
    super.new(name, parent);
    // Policy-change and reset phases add deliberately stalled requests to each RAM pass.
    test_timeout = 2ms;
  endfunction

  virtual function void configure_env_cfg(usb_env_cfg cfg);
    // Keep the directed case matrix deterministic; overlap uses explicit stalls.
    cfg.axi_delay_random = 1'b0;
  endfunction

  task run_phase(uvm_phase phase);
    usb_axi_dev_ram_rw_seq seq;

    phase.raise_objection(this);
    `uvm_info("USB_TEST", "Starting DEV0 and DEV1 RAM AXI cases with overlap, hazards, in-flight policy changes, and a reset with requests outstanding", UVM_LOW)
    env.wait_for_reset();
    scenario_completed = 1'b0;
    seq = usb_axi_dev_ram_rw_seq::type_id::create("dev_ram_rw_sequence");
    seq.start(env.virtual_sequencer);
    scenario_completed = seq.completed;
    phase.drop_objection(this);
  endtask
endclass
