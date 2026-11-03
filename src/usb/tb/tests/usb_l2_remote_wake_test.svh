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

class usb_l2_remote_wake_cfg_builder extends usb_vip_cfg_builder;
  `uvm_object_utils(usb_l2_remote_wake_cfg_builder)

  function new(string name = "usb_l2_remote_wake_cfg_builder");
    super.new(name);
  endfunction

  // Keep native scaled idle/recovery; override only external-DUT resume compatibility.
  // This is an accelerated functional profile, not nominal USB timing compliance.
  protected virtual function void configure_timers();
    svt_usb_configuration resume_cfgs[2];

    super.configure_timers();
    resume_cfgs[0] = host_cfg;
    resume_cfgs[1] = device_phy_cfg;
    foreach (resume_cfgs[index]) begin
      // The external DUT is not scaled: retain native upstream 1..15 ms checks.
      resume_cfgs[index].tdrsmup_min = vip_ps(1ms);
      resume_cfgs[index].tdrsmup_max = vip_ps(15ms);
      resume_cfgs[index].tdrsmup = vip_ps(1ms);
      resume_cfgs[index].tdrsmup_min_longint = longint'(vip_ps(1ms));
      resume_cfgs[index].tdrsmup_max_longint = longint'(vip_ps(15ms));
      resume_cfgs[index].tdrsmup_longint = longint'(vip_ps(1ms));
      resume_cfgs[index].tdrsmdn = vip_ps(usb_l2_remote_wake_host_seq::ACCELERATED_HOST_RESUME_BUDGET);
      resume_cfgs[index].tdrsmdn_min = resume_cfgs[index].tdrsmdn;
      resume_cfgs[index].tdrsmdn_nom = resume_cfgs[index].tdrsmdn;
      resume_cfgs[index].tdrsmdn_longint = longint'(resume_cfgs[index].tdrsmdn);
      resume_cfgs[index].tdrsmdn_min_longint = resume_cfgs[index].tdrsmdn_longint;
      resume_cfgs[index].tdrsmdn_nom_longint = resume_cfgs[index].tdrsmdn_longint;
      resume_cfgs[index].block_resume = 1'b0;
    end
    // Software recovery excludes device accesses, not resumed bus framing.
    host_cfg.enable_sof_during_recovery = 1'b1;
  endfunction
endclass

class usb_l2_remote_wake_test extends usb_base_test;
  `uvm_component_utils(usb_l2_remote_wake_test)

  function new(string name = "usb_l2_remote_wake_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 60ms;
  endfunction

  function void build_phase(uvm_phase phase);
    usb_vip_cfg_builder::type_id::set_type_override(usb_l2_remote_wake_cfg_builder::get_type());
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    usb_l2_remote_wake_seq sequence_handle;

    phase.raise_objection(this);
    env.wait_for_reset();
    sequence_handle = usb_l2_remote_wake_seq::type_id::create("remote_wake_sequence");
    sequence_handle.start(env.virtual_sequencer);
    scenario_completed = sequence_handle.completed;
    phase.drop_objection(this);
  endtask
endclass
