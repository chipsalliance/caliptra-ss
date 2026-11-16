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

// Verifies DEV0 enters L1, responds to host exit, and accepts traffic.
class usb_l1_host_resume_test extends usb_base_test;
  `uvm_component_utils(usb_l1_host_resume_test)

  function new(string name = "usb_l1_host_resume_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 3ms;
  endfunction

  // Select legacy HIRD=1 timing before the environment builds either VIP peer.
  virtual function void configure_env_cfg(usb_env_cfg cfg);
    super.configure_env_cfg(cfg);
    cfg.lpm_timing_policy = usb_env_cfg::USB_LPM_TIMING_LEGACY_HIRD1;
  endfunction

  virtual function time full_speed_timeout();
    return USB_FS_ENUMERATION_BUDGET + USB_FS_LPM_DISCOVERY_BUDGET +
      USB_FS_L1_CYCLE_TIMEOUT + USB_FS_TRANSFER_TIMEOUT + USB_FS_FRAME_PERIOD;
  endfunction

  task run_phase(uvm_phase phase);
    usb_l1_host_resume_seq resume_sequence;

    phase.raise_objection(this);
    `uvm_info("USB_L1_TEST", $sformatf("Starting L1 host-resume test; timeout=%0t", test_timeout), UVM_LOW)
    env.wait_for_reset();
    if (env_cfg.speed == USB_SPEED_FULL) begin
      usb_host_resume_seq shared_sequence;
      shared_sequence = usb_host_resume_seq::type_id::create("resume_sequence");
      shared_sequence.l1 = 1'b1;
      shared_sequence.suspend_timeout = USB_FS_L1_CYCLE_TIMEOUT;
      shared_sequence.start(env.virtual_sequencer);
      scenario_completed = shared_sequence.completed;
    end else begin
      resume_sequence = usb_l1_host_resume_seq::type_id::create("resume_sequence");
      resume_sequence.start(env.virtual_sequencer);
      scenario_completed = resume_sequence.completed;
    end
    `uvm_info("USB_L1_TEST", "L1 host-resume sequence returned; entering final UVM checks", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
