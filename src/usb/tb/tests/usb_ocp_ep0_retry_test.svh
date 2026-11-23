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

class usb_ocp_ep0_retry_vip_cfg_builder extends usb_ocp_base_vip_cfg_builder;
  `uvm_object_utils(usb_ocp_ep0_retry_vip_cfg_builder)
  localparam time DEVICE_TIMEOUT = 100us;

  function new(string name = "usb_ocp_ep0_retry_vip_cfg_builder");
    super.new(name);
  endfunction

  protected virtual function void configure_endpoints(usb_env_cfg cfg);
    super.configure_endpoints(cfg);
    // A deliberate received-handshake loss must retry before the enclosing
    // CONTROL watchdog, rather than consuming its entire 100ms bound.
    host_cfg.remote_device_cfg[1].device_timeout = vip_ps(DEVICE_TIMEOUT);
  endfunction
endclass

class usb_ocp_ep0_retry_test extends usb_ocp_base_test;
  `uvm_component_utils(usb_ocp_ep0_retry_test)

  function new(string name = "usb_ocp_ep0_retry_test", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  function void build_phase(uvm_phase phase);
    usb_ocp_observer::type_id::set_type_override(usb_ocp_ep0_retry_observer::get_type());
    usb_ocp_base_vip_cfg_builder::type_id::set_type_override(
      usb_ocp_ep0_retry_vip_cfg_builder::get_type());
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    usb_ocp_ep0_retry_seq scenario;
    phase.raise_objection(this);
    env.wait_for_reset();
    scenario = usb_ocp_ep0_retry_seq::type_id::create("scenario");
    scenario.start(env.virtual_sequencer);
    scenario_completed = scenario.completed;
    phase.drop_objection(this);
  endtask
endclass
