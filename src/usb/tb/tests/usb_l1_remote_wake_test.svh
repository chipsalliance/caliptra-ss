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

class usb_l1_remote_wake_test extends usb_base_test;
  `uvm_component_utils(usb_l1_remote_wake_test)

  function new(string name = "usb_l1_remote_wake_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 5ms;
  endfunction

  // Select legacy LPM timing before the environment builds either VIP peer.
  virtual function void configure_env_cfg(usb_env_cfg cfg);
    super.configure_env_cfg(cfg);
    cfg.lpm_timing_policy = usb_env_cfg::USB_LPM_TIMING_LEGACY_HIRD1;
  endfunction

  task run_phase(uvm_phase phase);
    usb_l1_remote_wake_seq wake_sequence;

    phase.raise_objection(this);
    env.wait_for_reset();
    wake_sequence = usb_l1_remote_wake_seq::type_id::create("wake_sequence");
    wake_sequence.start(env.virtual_sequencer);
    scenario_completed = wake_sequence.completed;
    phase.drop_objection(this);
  endtask
endclass
