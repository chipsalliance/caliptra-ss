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
// Configuration for one usb_axi_user_filter_agent. The environment sets vif
// and passes the object to the agent through config_db field "cfg".
class usb_axi_user_filter_agent_cfg #(
  int unsigned UW = 32,
  int unsigned NUM_USERS = 2
) extends uvm_object;
  `uvm_object_param_utils(usb_axi_user_filter_agent_cfg #(UW, NUM_USERS))

  virtual usb_axi_user_filter_if #(.UW(UW), .NUM_USERS(NUM_USERS)) vif;
  // A passive agent only monitors; the policy keeps the interface defaults.
  uvm_active_passive_enum is_active = UVM_ACTIVE;

  function new(string name = "usb_axi_user_filter_agent_cfg");
    super.new(name);
  endfunction
endclass
