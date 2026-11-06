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

class usb_ocp_base_vip_cfg_builder extends usb_vip_cfg_builder;
  `uvm_object_utils(usb_ocp_base_vip_cfg_builder)

  function new(string name = "usb_ocp_base_vip_cfg_builder");
    super.new(name);
  endfunction

  protected virtual function void configure_endpoints(usb_env_cfg cfg);
    usb_ocp_base_env_cfg ocp_cfg;
    usb_ocp_base_device_cfg device;
    usb_ocp_base_endpoint_cfg ep;
    if (!$cast(ocp_cfg, cfg))
      `uvm_fatal("OCP_CFG", "OCP builder requires OCP configuration")
    super.configure_endpoints(cfg);
    host_cfg.remote_device_cfg[0].device_timeout = vip_ps(100ms);
    host_cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_nak = 100000;
    for (int i = 1; i < 3; i++) begin
      device = usb_ocp_base_device_cfg::type_id::create($sformatf("device%0d", i-1));
      ep = usb_ocp_base_endpoint_cfg::type_id::create($sformatf("device%0d_ep0", i-1));
      device.device_address = ocp_cfg.parked_address[i];
      device.connected_bus_speed = svt_usb_types::HS;
      device.functionality_support = svt_usb_types::HS;
      device.connected_hub_device_address = ocp_cfg.assigned_address[0];
      device.hub_port_number = i;
      device.device_timeout = vip_ps(100ms);
      device.num_endpoints = 1;
      ep.ep_number = 0;
      ep.direction = svt_usb_types::IN;
      ep.ep_type = svt_usb_types::CONTROL;
      ep.speed = svt_usb_types::HS;
      ep.max_packet_size = 64;
      ep.interval = 1;
      ep.max_retry_due_to_nak = 100000;
      device.endpoint_cfg[0] = ep;
      host_cfg.remote_device_cfg.push_back(device);
    end
    host_cfg.remote_device_cfg_size = 3;
  endfunction

endclass
