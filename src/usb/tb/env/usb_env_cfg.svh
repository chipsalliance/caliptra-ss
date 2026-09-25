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

// Centralize the paired VIP settings, declarative endpoint profile, and
// simulation timers.
class usb_env_cfg extends uvm_object;
  `uvm_object_utils(usb_env_cfg)

  // VIP timing fields below use picoseconds, independent of the named duration.
  localparam real USB_TIMER_10US_PS  = 10000000.0;
  localparam real USB_TIMER_20US_PS  = 20000000.0;
  localparam real USB_TIMER_50US_PS  = 50000000.0;
  localparam real USB_TIMER_100US_PS = 100000000.0;
  localparam real USB_TIMER_150US_PS = 150000000.0;
  localparam real USB_TIMER_300US_PS = 300000000.0;

  // Declarative device endpoint layout. This queue is the single source of
  // truth for which endpoints the bench advertises, in what order they occupy
  // the SVT endpoint_cfg[] anchor array, and how each maps onto a DEV0
  // physical endpoint. Sequences resolve endpoints through get_endpoint()
  // rather than embedding literal anchor or physical indices, so the layout
  // can be reordered or extended without touching any sequence.
  //
  // A test that needs a different layout overrides build_endpoint_profile()
  // or edits endpoint_profile before usb_env calls configure_usb_vip().
  usb_endpoint_profile endpoint_profile[$];

  // usb_env installs host_cfg and clones device_phy_cfg as the remote PHY.
  svt_usb_agent_configuration host_cfg;
  svt_usb_agent_configuration device_phy_cfg;

  function new(string name = "usb_env_cfg");
    super.new(name);
  endfunction

  // -----------------------------------------------------------------------------
  // Endpoint profile construction and lookup
  // -----------------------------------------------------------------------------

  function int unsigned endpoint_count();
    return endpoint_profile.size();
  endfunction

  // Append one endpoint and hand back the profile so a caller can adjust any
  // remaining field before the profile is applied.
  function usb_endpoint_profile add_endpoint(usb_endpoint_profile endpoint);
    if (endpoint == null) begin
      `uvm_fatal("USB_CFG", "Cannot add a null endpoint profile")
    end
    endpoint_profile.push_back(endpoint);
    return endpoint;
  endfunction

  // The bench's default device: an EP0 control endpoint for enumeration plus a
  // bulk IN/OUT pair on EP1. Overriding this function is the supported way to
  // advertise a different device without editing any sequence.
  virtual function void build_endpoint_profile();
    endpoint_profile.delete();

    void'(add_endpoint(usb_endpoint_profile::create_endpoint(
      "ep0_control",
      0,
      USB_EP_DIR_OUT,
      USB_EP_KIND_CONTROL,
      `SVT_USB_HS_CONTROL_MAX_PACKET_SIZE,
      1,
      1'b0,
      0
    )));
    void'(add_endpoint(usb_endpoint_profile::create_endpoint(
      "ep1_bulk_in",
      1,
      USB_EP_DIR_IN,
      USB_EP_KIND_BULK,
      `SVT_USB_HS_BULK_MAX_PACKET_SIZE
    )));
    // The device does not require a terminating zero-length packet after a
    // max-packet-aligned bulk OUT transfer; without this the VIP forces one.
    void'(add_endpoint(usb_endpoint_profile::create_endpoint(
      "ep1_bulk_out",
      1,
      USB_EP_DIR_OUT,
      USB_EP_KIND_BULK,
      `SVT_USB_HS_BULK_MAX_PACKET_SIZE,
      1,
      1'b1
    )));
  endfunction

  // Reject layouts that cannot be represented before any of them reaches the
  // VIP or a sequence, so a profile mistake fails with its own diagnostic
  // rather than as an obscure VIP or CSR symptom.
  function void validate_endpoint_profile();
    bit physical_index_used[int unsigned];
    bit control_endpoint_present;

    if (endpoint_profile.size() == 0) begin
      `uvm_fatal("USB_CFG", "The endpoint profile is empty; at least a control endpoint is required")
    end

    foreach (endpoint_profile[index]) begin
      usb_endpoint_profile endpoint;
      int unsigned physical_index;

      endpoint = endpoint_profile[index];
      if (endpoint == null) begin
        `uvm_fatal("USB_CFG", $sformatf("Endpoint profile entry %0d is null", index))
      end
      physical_index = endpoint.physical_index();

      // NBPHYSEP counts only non-EP0 directions; the controller adds the two
      // EP0 halves, giving physical indices 0..NBPHYSEP+1.
      if (physical_index >= USB_DEV0_NBPHYSEP + 2) begin
        `uvm_fatal("USB_CFG", $sformatf("%s exceeds the DEV0 physical endpoint count of %0d (NBPHYSEP=%0d plus EP0 OUT/IN)", endpoint.describe(), USB_DEV0_NBPHYSEP + 2, USB_DEV0_NBPHYSEP))
      end
      if (physical_index_used.exists(physical_index)) begin
        `uvm_fatal("USB_CFG", $sformatf("%s duplicates an endpoint already claiming physical index %0d", endpoint.describe(), physical_index))
      end
      physical_index_used[physical_index] = 1'b1;

      if (endpoint.max_packet_size == 0) begin
        `uvm_fatal("USB_CFG", $sformatf("%s has a zero maximum packet size", endpoint.describe()))
      end
      if (endpoint.ep_kind == USB_EP_KIND_CONTROL) begin
        if (endpoint.ep_number != 0) begin
          `uvm_fatal("USB_CFG", $sformatf("%s is a control endpoint on a non-zero endpoint number", endpoint.describe()))
        end
        control_endpoint_present = 1'b1;
      end
    end

    if (!control_endpoint_present) begin
      `uvm_fatal("USB_CFG", "The endpoint profile has no control endpoint, so enumeration cannot run")
    end
  endfunction

  // Return the endpoint matching a protocol identity, or null when the bench is
  // not advertising it. A control endpoint matches either direction because one
  // profile entry covers both halves of EP0; the result is bound to the
  // requested direction so every derived DUT address and bit follows it.
  function usb_endpoint_profile find_endpoint(int unsigned ep_number, usb_ep_dir_e direction);
    foreach (endpoint_profile[index]) begin
      usb_endpoint_profile endpoint;

      endpoint = endpoint_profile[index];
      if (endpoint.ep_number != ep_number) begin
        continue;
      end
      if (endpoint.ep_kind == USB_EP_KIND_CONTROL) begin
        return endpoint.view_for_direction(direction);
      end
      if (endpoint.direction == direction) begin
        return endpoint;
      end
    end
    return null;
  endfunction

  // Checked lookup for sequences. Failing here names the requested endpoint and
  // lists what the profile does advertise, so a mismatch is diagnosable without
  // reading the configuration source.
  function usb_endpoint_profile get_endpoint(int unsigned ep_number, usb_ep_dir_e direction);
    usb_endpoint_profile endpoint;

    endpoint = find_endpoint(ep_number, direction);
    if (endpoint == null) begin
      `uvm_fatal("USB_CFG", $sformatf("EP%0d %s is not in the endpoint profile. Advertised endpoints: %s", ep_number, (direction == USB_EP_DIR_IN) ? "IN" : "OUT", describe_endpoint_profile()))
    end
    return endpoint;
  endfunction

  function usb_endpoint_profile get_endpoint_by_anchor(int unsigned anchor_index);
    if (anchor_index >= endpoint_profile.size()) begin
      `uvm_fatal("USB_CFG", $sformatf("Anchor index %0d is outside the %0d-endpoint profile", anchor_index, endpoint_profile.size()))
    end
    return endpoint_profile[anchor_index];
  endfunction

  function string describe_endpoint_profile();
    string description;

    foreach (endpoint_profile[index]) begin
      description = {description, (index == 0) ? "" : ", ", endpoint_profile[index].describe()};
    end
    return description;
  endfunction

  // Translate the profile into the VIP's endpoint configuration array. This is
  // the only function that names svt_usb_types endpoint values, and it assigns
  // each profile's anchor index as a side effect so the assignment and the
  // recorded index cannot disagree.
  function void apply_endpoint_profile();
    validate_endpoint_profile();

    device_phy_cfg.local_device_cfg[0].num_endpoints = endpoint_count();

    foreach (endpoint_profile[anchor]) begin
      usb_endpoint_profile endpoint;

      endpoint = endpoint_profile[anchor];
      endpoint.anchor_index = anchor;
      endpoint.anchor_index_valid = 1'b1;

      device_phy_cfg.local_device_cfg[0].endpoint_cfg[anchor] = new();
      device_phy_cfg.local_device_cfg[0].endpoint_cfg[anchor].ep_number = endpoint.ep_number;
      device_phy_cfg.local_device_cfg[0].endpoint_cfg[anchor].direction =
          endpoint.svt_direction_is_in() ? svt_usb_types::IN : svt_usb_types::OUT;
      // Only the transfer types this bench has exercised are mapped. Adding a
      // type is a single case arm here plus the matching usb_ep_kind_e member.
      case (endpoint.ep_kind)
        USB_EP_KIND_CONTROL: device_phy_cfg.local_device_cfg[0].endpoint_cfg[anchor].ep_type = svt_usb_types::CONTROL;
        USB_EP_KIND_BULK:    device_phy_cfg.local_device_cfg[0].endpoint_cfg[anchor].ep_type = svt_usb_types::BULK;
        default: `uvm_fatal("USB_CFG", $sformatf("%s uses a transfer type with no SVT mapping in apply_endpoint_profile()", endpoint.describe()))
      endcase
      device_phy_cfg.local_device_cfg[0].endpoint_cfg[anchor].interval = endpoint.interval;
      device_phy_cfg.local_device_cfg[0].endpoint_cfg[anchor].max_packet_size = endpoint.max_packet_size;
      device_phy_cfg.local_device_cfg[0].endpoint_cfg[anchor].speed = svt_usb_types::HS;
      if (endpoint.max_burst_size_valid) begin
        device_phy_cfg.local_device_cfg[0].endpoint_cfg[anchor].max_burst_size = endpoint.max_burst_size;
      end
      if (endpoint.allow_aligned_transfer_without_zero_length) begin
        device_phy_cfg.local_device_cfg[0].endpoint_cfg[anchor].allow_aligned_transfer_without_zero_length = 1;
      end
    end

    `uvm_info("USB_CFG", $sformatf("Applied a %0d-endpoint device profile: %s", endpoint_count(), describe_endpoint_profile()), UVM_LOW)
  endfunction

  // Create the paired USB 2.0 HS configurations, apply the declarative endpoint
  // profile, and set scaled timers and tracing. Call before validate_usb_vip().
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
    device_phy_cfg.local_device_cfg[0].device_timeout = USB_TIMER_50US_PS;

    // Build the layout only when a test has not already supplied one, then
    // translate it into the VIP's endpoint array.
    if (endpoint_profile.size() == 0) begin
      build_endpoint_profile();
    end
    apply_endpoint_profile();

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
