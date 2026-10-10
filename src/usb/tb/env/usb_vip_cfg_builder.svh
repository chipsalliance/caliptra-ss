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
//
// Translates usb_env_cfg into the paired Synopsys SVT USB 2.0 configurations:
// the local host installed on the host agent and the remote UTMI device PHY.
// This is the only bench object that names svt_usb_types endpoint values, so
// a VIP change is confined here. usb_env creates it through the factory, so
// a test can override the VIP setup without editing the environment.

class usb_vip_cfg_builder extends uvm_object;
  `uvm_object_utils(usb_vip_cfg_builder)

  // Results of build(); usb_env installs host_cfg and derives the remote PHY
  // configuration from device_phy_cfg.
  svt_usb_agent_configuration host_cfg;
  svt_usb_agent_configuration device_phy_cfg;

  function new(string name = "usb_vip_cfg_builder");
    super.new(name);
  endfunction

  // SVT timing fields are real picoseconds.
  static function real vip_ps(time duration);
    return duration / 1ps;
  endfunction

  // Validate cfg, record its VIP anchors, and build both SVT configurations.
  virtual function void build(usb_env_cfg cfg);
    if (cfg == null) begin
      `uvm_fatal("USB_CFG", "usb_vip_cfg_builder::build() requires a usb_env_cfg")
    end
    cfg.validate();
    cfg.assign_anchor_indices();

    host_cfg = new();
    device_phy_cfg = new();
    configure_topology();
    configure_endpoints(cfg);
    configure_timers();
    configure_tracing();
    configure_coverage();
    validate_vip_cfgs();
  endfunction

  // One local high-speed host and one remote device, with no hub between.
  // Both sides use 8-bit USB 2.0 only; the host uses TLM and the remote
  // device connects through UTMI. The device starts at the default address
  // zero for enumeration.
  protected virtual function void configure_topology();
    host_cfg.component_type = svt_usb_types::HOST;
    device_phy_cfg.component_type = svt_usb_types::DEVICE;
    host_cfg.top_layer = svt_usb_agent_configuration::PROTOCOL;
    device_phy_cfg.top_layer = svt_usb_agent_configuration::PROTOCOL;

    host_cfg.local_host_cfg = new();
    host_cfg.local_host_cfg.high_speed_capable = 1'b1;
    host_cfg.local_device_cfg_size = 0;

    device_phy_cfg.local_device_cfg_size = 1;
    device_phy_cfg.local_device_cfg[0] = new();
    device_phy_cfg.local_host_cfg = null;

    // Share the peer descriptions so both sides refer to the same device/host.
    host_cfg.remote_device_cfg_size = device_phy_cfg.local_device_cfg_size;
    host_cfg.remote_device_cfg = device_phy_cfg.local_device_cfg;
    host_cfg.remote_host_cfg = device_phy_cfg.local_host_cfg;
    device_phy_cfg.remote_host_cfg = host_cfg.local_host_cfg;
    device_phy_cfg.remote_device_cfg_size = host_cfg.local_device_cfg_size;

    host_cfg.capability = svt_usb_configuration::PLAIN;
    host_cfg.speed = svt_usb_types::HS;
    host_cfg.usb_20_signal_interface = svt_usb_configuration::USB_20_TLM;
    host_cfg.usb_ss_signal_interface = svt_usb_configuration::NO_SS_IF;
    host_cfg.usb_capability = svt_usb_configuration::USB_20_ONLY;
    host_cfg.utmi_data_width = 8;
    host_cfg.poweron_auto_attach_delay = vip_ps(20us);

    device_phy_cfg.capability = svt_usb_configuration::PLAIN;
    device_phy_cfg.speed = svt_usb_types::HS;
    device_phy_cfg.usb_20_signal_interface = svt_usb_configuration::UTMI_IF;
    device_phy_cfg.usb_ss_signal_interface = svt_usb_configuration::NO_SS_IF;
    device_phy_cfg.usb_capability = svt_usb_configuration::USB_20_ONLY;
    device_phy_cfg.utmi_data_width = 8;
    device_phy_cfg.poweron_auto_attach_delay = vip_ps(20us);

    device_phy_cfg.local_device_cfg[0].connected_bus_speed = svt_usb_types::HS;
    device_phy_cfg.local_device_cfg[0].functionality_support = svt_usb_types::HS;
    device_phy_cfg.local_device_cfg[0].device_address = 0;
    device_phy_cfg.local_device_cfg[0].connected_hub_device_address = 0;
    device_phy_cfg.local_device_cfg[0].device_timeout = vip_ps(50us);
  endfunction

  // Fill the VIP's endpoint_cfg[] array at the anchors recorded in cfg.
  protected virtual function void configure_endpoints(usb_env_cfg cfg);
    device_phy_cfg.local_device_cfg[0].num_endpoints = 1 + cfg.generic_endpoint_count();
    // SVT declares its bidirectional control endpoint as IN.
    configure_vip_endpoint(cfg.ep0_in_cfg);
    foreach (cfg.endpoint_cfgs[index]) begin
      configure_vip_endpoint(cfg.endpoint_cfgs[index]);
    end
    `uvm_info("USB_CFG", $sformatf("Applied control endpoint plus %0d generic endpoints: %s", cfg.generic_endpoint_count(), cfg.describe_endpoint_cfgs()), UVM_LOW)
  endfunction

  // Write one SVT endpoint_cfg[] slot.
  protected virtual function void configure_vip_endpoint(usb_endpoint_cfg endpoint);
    svt_usb_endpoint_configuration vip_endpoint;

    if (!endpoint.anchor_index_valid) begin
      `uvm_fatal("USB_CFG", $sformatf("%s has no VIP anchor; call usb_env_cfg::assign_anchor_indices() first", endpoint.convert2string()))
    end
    // Vendor configuration classes are not factory-registered, so new() is
    // used for every SVT object built here.
    vip_endpoint = new();
    vip_endpoint.ep_number = endpoint.ep_number;
    vip_endpoint.direction = (endpoint.direction == USB_DIRECTION_IN) ? svt_usb_types::IN : svt_usb_types::OUT;
    // Only the transfer types this bench has exercised are mapped. Adding a
    // type is one case arm here plus the matching usb_transfer_type_e member.
    case (endpoint.transfer_type)
      USB_TRANSFER_TYPE_CONTROL: vip_endpoint.ep_type = svt_usb_types::CONTROL;
      USB_TRANSFER_TYPE_BULK:    vip_endpoint.ep_type = svt_usb_types::BULK;
      default: `uvm_fatal("USB_CFG", $sformatf("%s uses a transfer type with no SVT mapping in configure_vip_endpoint()", endpoint.convert2string()))
    endcase
    vip_endpoint.interval = endpoint.interval;
    vip_endpoint.max_packet_size = endpoint.max_packet_size;
    vip_endpoint.speed = svt_usb_types::HS;
    if (endpoint.max_burst_size_valid) begin
      vip_endpoint.max_burst_size = endpoint.max_burst_size;
    end
    if (endpoint.allow_aligned_transfer_without_zero_length) begin
      vip_endpoint.allow_aligned_transfer_without_zero_length = 1;
    end
    device_phy_cfg.local_device_cfg[0].endpoint_cfg[endpoint.anchor_index] = vip_endpoint;
  endfunction

  // Apply the vendor's scaled timer set first, then the bench-specific
  // attach/reset/handshake/inactivity values symmetrically on both sides.
  protected virtual function void configure_timers();
    void'(host_cfg.set_timer_values(svt_usb_configuration::USB_VIP_SCALEDOWN_TIMER_VALUES));
    void'(device_phy_cfg.set_timer_values(svt_usb_configuration::USB_VIP_SCALEDOWN_TIMER_VALUES));
    host_cfg.tsigatt = vip_ps(100us);
    device_phy_cfg.tsigatt = vip_ps(100us);
    host_cfg.tdrst = vip_ps(150us);
    device_phy_cfg.tdrst = vip_ps(150us);
    host_cfg.twtdch = vip_ps(10us);
    device_phy_cfg.twtdch = vip_ps(10us);
    host_cfg.twths = vip_ps(10us);
    device_phy_cfg.twths = vip_ps(10us);
    host_cfg.tinactivity = vip_ps(300us);
    device_phy_cfg.tinactivity = vip_ps(300us);
  endfunction

  // Retain protocol-through-PHY traces on both sides for live USB debug.
  protected virtual function void configure_tracing();
    host_cfg.enable_prot_tracing = 1;
    host_cfg.enable_link_tracing = 1;
    host_cfg.enable_phys_tracing = 1;
    host_cfg.enable_phys_reporting = 1;
    host_cfg.enable_runtime_trace_recording = 1;
    device_phy_cfg.enable_prot_tracing = 1;
    device_phy_cfg.enable_link_tracing = 1;
    device_phy_cfg.enable_phys_tracing = 1;
    device_phy_cfg.enable_phys_reporting = 1;
    device_phy_cfg.enable_runtime_trace_recording = 1;
  endfunction

  // Enable the VIP's built-in protocol and link layer functional coverage on both sides.
  protected virtual function void configure_coverage();
    host_cfg.enable_prot_cov = 1;
    host_cfg.enable_link_cov = 1;
    device_phy_cfg.enable_prot_cov = 1;
    device_phy_cfg.enable_link_cov = 1;
  endfunction

  // Reject vendor-invalid configurations before agent construction.
  protected virtual function void validate_vip_cfgs();
    if (!host_cfg.is_valid() || !device_phy_cfg.is_valid()) begin
      `uvm_fatal("USB_CFG", "USB VIP configuration validation failed")
    end
  endfunction
endclass
