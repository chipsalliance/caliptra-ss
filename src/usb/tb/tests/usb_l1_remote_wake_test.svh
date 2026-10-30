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

class usb_l1_remote_wake_vip_cfg_builder extends usb_vip_cfg_builder;
  `uvm_object_utils(usb_l1_remote_wake_vip_cfg_builder)

  function new(string name = "usb_l1_remote_wake_vip_cfg_builder");
    super.new(name);
  endfunction

  protected virtual function void configure_timers();
    super.configure_timers();
    restore_lpm_timers(host_cfg);
    restore_lpm_timers(device_phy_cfg);
  endfunction

  // Restore drive and checker limits together after the shared scaled preset.
  // USB 2.0 LPM ECN section 4.9, Table 4-6; SVT configuration tl1* members.
  function void restore_lpm_timers(svt_usb_configuration cfg);
    cfg.tl1tokenretry = vip_ps(8us);
    cfg.tl1tokenretry_min = vip_ps(8us);
    cfg.tl1residency = vip_ps(50us);
    cfg.tl1residency_min = vip_ps(50us);
    cfg.tl1residency_max = vip_ps(55us);
    cfg.tl1devdrvresume = vip_ps(50us);
    cfg.tl1devdrvresume_min = vip_ps(50us);
    cfg.tl1hubreflect = vip_ps(30us);
    cfg.tl1hubreflect_min = vip_ps(30us);
    cfg.tl1hubreflect_max = vip_ps(48us);
    cfg.tl1hubdrvresume2 = vip_ps(60us);
    cfg.tl1hubdrvresume2_min = vip_ps(60us);
    cfg.tl1hubdrvresume2_max = vip_ps(990us);
    cfg.tl1exitdevrecovery = vip_ps(10us);
    cfg.tl1exitdevrecovery_min = vip_ps(10us);
  endfunction
endclass

class usb_l1_remote_wake_test extends usb_base_test;
  `uvm_component_utils(usb_l1_remote_wake_test)

  function new(string name = "usb_l1_remote_wake_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 5ms;
  endfunction

  function void build_phase(uvm_phase phase);
    usb_vip_cfg_builder::type_id::set_type_override(usb_l1_remote_wake_vip_cfg_builder::get_type());
    super.build_phase(phase);
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
