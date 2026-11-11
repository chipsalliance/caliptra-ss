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

class usb_ocp_base_env_cfg extends usb_env_cfg;
  `uvm_object_utils(usb_ocp_base_env_cfg)
  virtual usb_ocp_recovery_if recovery_vif;
  usb_ocp_base_epn_profile epn_profile;
  // Firmware lifecycle only; never acceptance or overlap evidence.
  logic epn_enabled[2] = '{default:0};
  logic epn_ready[2][2][2] = '{default:'{default:'{default:0}}};
  logic epn_service_finished[2] = '{default:0};

  // Stable VIP slots: hub, downstream port 1, downstream port 2.
  // Unenumerated slots use distinct parking addresses, never shared address 0.
  logic [6:0] assigned_address[3] = '{7'd1, 7'd2, 7'd3};
  logic [6:0] parked_address[3] = '{7'd0, 7'd126, 7'd127};
  logic prepared[3] = '{default: 1'b0};
  logic stop_requested = 1'b0;
  logic actor_finished[4] = '{default: 1'b0};
  time actor_timeout = 2s;
  time service_poll = 2us;
  // Firmware idle pacing only; USB reset/debounce/recovery timers are separate.
  time idle_poll_max = 1ms;
  time service_gap_max = 10us;

  function new(string name = "usb_ocp_base_env_cfg");
    super.new(name);
    link_timeout = 300ms;
    vbus_timeout = 300ms;
    control_transfer_timeout = 100ms;
    transfer_timeout = 100us;
  endfunction

  virtual function void build_endpoint_cfgs();
    build_control_endpoint_cfgs();
    endpoint_cfgs.delete();
  endfunction
endclass
