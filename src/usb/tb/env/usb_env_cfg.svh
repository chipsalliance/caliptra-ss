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
// Configuration for the compound USB unitbench's Synopsys SVT USB path.
// Included by usb_tb_pkg.sv and owned by usb_env, this object prepares a USB 2.0
// high-speed host plus the remote UTMI device-PHY configuration used for INIT.

// Centralize the paired VIP settings, endpoint template, and simulation timers.
class usb_env_cfg extends uvm_object;
  `uvm_object_utils(usb_env_cfg)

  // VIP timing fields below use picoseconds, independent of the named duration.
  localparam real USB_TIMER_10US_PS  = 10000000.0;
  localparam real USB_TIMER_20US_PS  = 20000000.0;
  localparam real USB_TIMER_50US_PS  = 50000000.0;
  localparam real USB_TIMER_100US_PS = 100000000.0;
  localparam real USB_TIMER_150US_PS = 150000000.0;
  localparam real USB_TIMER_300US_PS = 300000000.0;

  // The template below requires EP0 and EP1; extra entries need configuration.
  int unsigned endpoint_count = 2;

  // usb_env installs host_cfg and clones device_phy_cfg as the remote PHY.
  svt_usb_agent_configuration host_cfg;
  svt_usb_agent_configuration device_phy_cfg;

  function new(string name = "usb_env_cfg");
    super.new(name);
  endfunction

  // Create the paired USB 2.0 HS configurations, EP0 control/EP1 bulk-IN
  // template, scaled timers, and tracing. Call before validate_usb_vip().
  function void configure_usb_vip();
    host_cfg = new();
    device_phy_cfg = new();

    host_cfg.component_type = svt_usb_types::HOST;
    device_phy_cfg.component_type = svt_usb_types::DEVICE;
    host_cfg.top_layer = svt_usb_agent_configuration::PROTOCOL;
    device_phy_cfg.top_layer = svt_usb_agent_configuration::PROTOCOL;

    // Model one local host and one remote device, with no hub in between.
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

    // The host uses USB 2.0 TLM; the remote device side connects through UTMI.
    // Both describe an 8-bit, high-speed USB 2.0 link with no SuperSpeed path.
    host_cfg.capability = svt_usb_configuration::PLAIN;
    host_cfg.speed = svt_usb_types::HS;
    host_cfg.usb_20_signal_interface = svt_usb_configuration::USB_20_TLM;
    host_cfg.usb_ss_signal_interface = svt_usb_configuration::NO_SS_IF;
    host_cfg.usb_capability = svt_usb_configuration::USB_20_ONLY;
    host_cfg.utmi_data_width = 8;
    host_cfg.poweron_auto_attach_delay = USB_TIMER_20US_PS;

    device_phy_cfg.capability = svt_usb_configuration::PLAIN;
    device_phy_cfg.speed = svt_usb_types::HS;
    device_phy_cfg.usb_20_signal_interface = svt_usb_configuration::UTMI_IF;
    device_phy_cfg.usb_ss_signal_interface = svt_usb_configuration::NO_SS_IF;
    device_phy_cfg.usb_capability = svt_usb_configuration::USB_20_ONLY;
    device_phy_cfg.utmi_data_width = 8;
    device_phy_cfg.poweron_auto_attach_delay = USB_TIMER_20US_PS;

    // Start with the device at address zero for the INIT enumeration flow.
    device_phy_cfg.local_device_cfg[0].connected_bus_speed = svt_usb_types::HS;
    device_phy_cfg.local_device_cfg[0].functionality_support = svt_usb_types::HS;
    device_phy_cfg.local_device_cfg[0].device_address = 0;
    device_phy_cfg.local_device_cfg[0].connected_hub_device_address = 0;
    device_phy_cfg.local_device_cfg[0].num_endpoints = endpoint_count;
    device_phy_cfg.local_device_cfg[0].device_timeout = USB_TIMER_50US_PS;

    for (int unsigned endpoint = 0; endpoint < endpoint_count; endpoint++) begin
      device_phy_cfg.local_device_cfg[0].endpoint_cfg[endpoint] = new();
    end
    // EP0 describes the control endpoint used for enumeration requests.
    device_phy_cfg.local_device_cfg[0].endpoint_cfg[0].ep_number = 0;
    device_phy_cfg.local_device_cfg[0].endpoint_cfg[0].direction = svt_usb_types::IN;
    device_phy_cfg.local_device_cfg[0].endpoint_cfg[0].ep_type = svt_usb_types::CONTROL;
    device_phy_cfg.local_device_cfg[0].endpoint_cfg[0].interval = 1;
    device_phy_cfg.local_device_cfg[0].endpoint_cfg[0].max_burst_size = 0;
    device_phy_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size = `SVT_USB_HS_CONTROL_MAX_PACKET_SIZE;
    device_phy_cfg.local_device_cfg[0].endpoint_cfg[0].speed = svt_usb_types::HS;

    // EP1 supplies the bulk-IN endpoint in the bench's device template.
    device_phy_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number = 1;
    device_phy_cfg.local_device_cfg[0].endpoint_cfg[1].direction = svt_usb_types::IN;
    device_phy_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type = svt_usb_types::BULK;
    device_phy_cfg.local_device_cfg[0].endpoint_cfg[1].interval = 1;
    device_phy_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = `SVT_USB_HS_BULK_MAX_PACKET_SIZE;
    device_phy_cfg.local_device_cfg[0].endpoint_cfg[1].speed = svt_usb_types::HS;

    // Apply the vendor's scaled timer set first, then the bench-specific
    // attach/reset/handshake/inactivity values symmetrically on both sides.
    void'(host_cfg.set_timer_values(svt_usb_configuration::USB_VIP_SCALEDOWN_TIMER_VALUES));
    void'(device_phy_cfg.set_timer_values(svt_usb_configuration::USB_VIP_SCALEDOWN_TIMER_VALUES));
    host_cfg.tsigatt = USB_TIMER_100US_PS;
    device_phy_cfg.tsigatt = USB_TIMER_100US_PS;
    host_cfg.tdrst = USB_TIMER_150US_PS;
    device_phy_cfg.tdrst = USB_TIMER_150US_PS;
    host_cfg.twtdch = USB_TIMER_10US_PS;
    device_phy_cfg.twtdch = USB_TIMER_10US_PS;
    host_cfg.twths = USB_TIMER_10US_PS;
    device_phy_cfg.twths = USB_TIMER_10US_PS;
    host_cfg.tinactivity = USB_TIMER_300US_PS;
    device_phy_cfg.tinactivity = USB_TIMER_300US_PS;

    // Retain protocol-through-PHY traces on both sides for live USB debug.
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

  // Reject missing or vendor-invalid configurations before agent construction.
  function void validate_usb_vip();
    if (host_cfg == null || device_phy_cfg == null) begin
      `uvm_fatal("USB_CFG", "USB VIP configurations were not constructed")
    end
    if (!host_cfg.is_valid() || !device_phy_cfg.is_valid()) begin
      `uvm_fatal("USB_CFG", "USB VIP configuration validation failed")
    end
  endfunction
endclass
