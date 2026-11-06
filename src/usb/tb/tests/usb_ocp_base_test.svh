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

class usb_ocp_base_test extends usb_base_test;
  `uvm_component_utils(usb_ocp_base_test)

  function new(string name = "usb_ocp_base_test", uvm_component parent = null);
    super.new(name,parent);
    test_timeout = 3s;
  endfunction

  function void build_phase(uvm_phase phase);
    // These instance overrides exist only when this OCP base test is selected.
    usb_env::type_id::set_inst_override(usb_ocp_base_env::get_type(),{get_full_name(),".env"});
    usb_env_cfg::type_id::set_inst_override(usb_ocp_base_env_cfg::get_type(),"env_cfg");
    usb_vip_cfg_builder::type_id::set_inst_override(usb_ocp_base_vip_cfg_builder::get_type(),"vip_cfg_builder");
    super.build_phase(phase);
  endfunction
endclass
