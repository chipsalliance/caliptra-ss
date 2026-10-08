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
// Configuration for the compound USB unitbench. usb_base_test creates this
// object, fills its defaults, and publishes it to usb_env through
// uvm_config_db. It holds only bench-level data: the advertised endpoint
// layout, the enumerated device address, the DEV0 endpoint-list placement,
// and the bench-wide timeouts. usb_vip_cfg_builder translates it into the
// Synopsys SVT agent configurations, so no VIP type is declared here.

class usb_env_cfg extends uvm_object;
  `uvm_object_utils(usb_env_cfg)

  // VIP anchor of the control endpoint. SVT requires endpoint_cfg[0] to be
  // the default control endpoint and models it as one bidirectional entry,
  // so both EP0 direction objects carry this anchor.
  localparam int unsigned CONTROL_ANCHOR_INDEX = 0;

  // EPLISTSTART.EP_LIST_PRG holds address bits [31:8], so the endpoint list
  // must start on a 256-byte boundary.
  localparam int unsigned ENDPOINT_LIST_ALIGNMENT = 256;

  // EP0 control endpoint, one object per direction. USB 2.0 fixes EP0 as the
  // default control pipe and the DEV0 endpoint list fixes its OUT, SETUP, and
  // IN entries at the head, so it is held apart from the generic endpoints.
  // The objects share usb_endpoint_cfg with the generic endpoints, so lookup
  // and DUT addressing are uniform.
  usb_endpoint_cfg ep0_out_cfg;
  usb_endpoint_cfg ep0_in_cfg;

  // Generic endpoints (EP1-EP15; bulk, interrupt, or isochronous), in VIP
  // anchor order after the control endpoint. Sequences resolve every endpoint
  // through get_endpoint() rather than literal anchor or physical indices, so
  // this list can be reordered or extended without touching any sequence.
  //
  // usb_base_test fills both with build_endpoint_cfgs() defaults; a test that
  // needs a different layout edits them in usb_base_test::configure_env_cfg()
  // before usb_env builds the VIP configuration.
  usb_endpoint_cfg endpoint_cfgs[$];

  // AXI manager delay randomization for every native and RAL request. A test
  // that needs exact stimulus clears it in configure_env_cfg();
  // +usb_axi_delay_random=0|1 overrides the test, and usb_env writes the
  // resolved value back here before building the managers.
  bit axi_delay_random = 1'b1;

  // Address the host assigns with SET_ADDRESS. Every host and device
  // sequence takes the enumerated address from here.
  bit [6:0] device_address = USB_DEFAULT_DEVICE_ADDRESS;

  // DEV0 packet-memory byte offset of the endpoint list (EPLISTSTART).
  logic [31:0] endpoint_list_base = 32'h0000_0000;

  // Bench-wide bounds. Adjust in usb_base_test::configure_env_cfg().
  //   reset_timeout            - usb_env manager reset release
  //   transfer_timeout         - every native and RAL access
  //   vbus_timeout             - VBUS detection before enumeration
  //   link_timeout             - host link enable after attach
  //   control_transfer_timeout - one host control transfer
  time reset_timeout = USB_DEFAULT_RESET_TIMEOUT;
  time transfer_timeout = USB_DEFAULT_TRANSFER_TIMEOUT;
  time vbus_timeout = USB_DEFAULT_VBUS_TIMEOUT;
  time link_timeout = USB_DEFAULT_LINK_TIMEOUT;
  time control_transfer_timeout = USB_DEFAULT_CONTROL_TRANSFER_TIMEOUT;

  function new(string name = "usb_env_cfg");
    super.new(name);
  endfunction

  // ---------------------------------------------------------------------------
  // Endpoint configuration construction and lookup
  // ---------------------------------------------------------------------------

  function int unsigned generic_endpoint_count();
    return endpoint_cfgs.size();
  endfunction

  // Append one generic endpoint and hand back its configuration so a caller
  // can adjust any remaining field before the endpoints are applied.
  function usb_endpoint_cfg add_endpoint(usb_endpoint_cfg endpoint);
    if (endpoint == null) begin
      `uvm_fatal("USB_CFG", "Cannot add a null endpoint configuration")
    end
    endpoint_cfgs.push_back(endpoint);
    return endpoint;
  endfunction

  // Build both EP0 direction objects with a shared maximum packet size.
  function void build_control_endpoint_cfgs(int unsigned max_packet_size = `SVT_USB_HS_CONTROL_MAX_PACKET_SIZE);
    ep0_out_cfg = usb_endpoint_cfg::create_endpoint("ep0_control_out", 0, USB_DIRECTION_OUT, USB_TRANSFER_TYPE_CONTROL, max_packet_size, 1, 1'b0, 0);
    ep0_in_cfg = usb_endpoint_cfg::create_endpoint("ep0_control_in", 0, USB_DIRECTION_IN, USB_TRANSFER_TYPE_CONTROL, max_packet_size, 1, 1'b0, 0);
  endfunction

  // The bench's default device: EP0 for enumeration plus a bulk IN/OUT pair
  // on EP1. A test advertises a different device by editing endpoint_cfgs
  // (or overriding this function) without editing any sequence.
  virtual function void build_endpoint_cfgs();
    build_control_endpoint_cfgs();
    endpoint_cfgs.delete();

    void'(add_endpoint(usb_endpoint_cfg::create_endpoint("ep1_bulk_in", 1, USB_DIRECTION_IN, USB_TRANSFER_TYPE_BULK, `SVT_USB_HS_BULK_MAX_PACKET_SIZE)));
    // The device does not require a terminating zero-length packet after a
    // max-packet-aligned bulk OUT transfer; without this the VIP forces one.
    void'(add_endpoint(usb_endpoint_cfg::create_endpoint("ep1_bulk_out", 1, USB_DIRECTION_OUT, USB_TRANSFER_TYPE_BULK, `SVT_USB_HS_BULK_MAX_PACKET_SIZE, 1, 1'b1)));
  endfunction

  // ---------------------------------------------------------------------------
  // Validation
  // ---------------------------------------------------------------------------

  // Reject any configuration that cannot be represented before it reaches
  // the VIP or a sequence, so a mistake fails with its own diagnostic rather
  // than as an obscure VIP or CSR symptom.
  function void validate();
    validate_endpoint_cfgs();
    if (device_address == 0) begin
      `uvm_fatal("USB_CFG", "device_address must be 1-127; address 0 is the default address before SET_ADDRESS")
    end
    if (endpoint_list_base % ENDPOINT_LIST_ALIGNMENT != 0) begin
      `uvm_fatal("USB_CFG", $sformatf("endpoint_list_base 0x%08h is not %0d-byte aligned as EPLISTSTART requires", endpoint_list_base, ENDPOINT_LIST_ALIGNMENT))
    end
    if (64'(endpoint_list_base) + endpoint_list_bytes() > USB_DEV0_RAM_DEPTH * (USB_PACKET_RAM_DATA_WIDTH / 8)) begin
      `uvm_fatal("USB_CFG", $sformatf("endpoint_list_base 0x%08h places the endpoint list beyond DEV0 packet memory", endpoint_list_base))
    end
    if (reset_timeout == 0 || transfer_timeout == 0 || vbus_timeout == 0 || link_timeout == 0 || control_transfer_timeout == 0) begin
      `uvm_fatal("USB_CFG", $sformatf("Every bench timeout must be nonzero: %s", convert2string()))
    end
  endfunction

  function void validate_endpoint_cfgs();
    bit physical_index_used[int unsigned];

    validate_control_endpoint_cfg(ep0_out_cfg, USB_DIRECTION_OUT);
    validate_control_endpoint_cfg(ep0_in_cfg, USB_DIRECTION_IN);
    if (ep0_out_cfg.max_packet_size != ep0_in_cfg.max_packet_size) begin
      `uvm_fatal("USB_CFG", $sformatf("EP0 OUT and IN maximum packet sizes differ (%0d vs %0d); the control pipe has one size", ep0_out_cfg.max_packet_size, ep0_in_cfg.max_packet_size))
    end

    foreach (endpoint_cfgs[index]) begin
      usb_endpoint_cfg endpoint;
      int unsigned physical_index;

      endpoint = endpoint_cfgs[index];
      if (endpoint == null) begin
        `uvm_fatal("USB_CFG", $sformatf("Generic endpoint configuration entry %0d is null", index))
      end
      if (endpoint.ep_number == 0 || endpoint.ep_number > 15) begin
        `uvm_fatal("USB_CFG", $sformatf("%s must use endpoint number 1-15; EP0 is configured through ep0_out_cfg/ep0_in_cfg", endpoint.convert2string()))
      end
      // DEV0 supports control transfers only on EP0; generic list entries
      // select only generic or periodic handling (Programmer's Guide 4.2.3).
      if (endpoint.transfer_type == USB_TRANSFER_TYPE_CONTROL) begin
        `uvm_fatal("USB_CFG", $sformatf("%s is a control endpoint; only EP0 may use control transfers", endpoint.convert2string()))
      end
      if (endpoint.max_packet_size == 0) begin
        `uvm_fatal("USB_CFG", $sformatf("%s has a zero maximum packet size", endpoint.convert2string()))
      end

      // NBPHYSEP counts only non-EP0 directions; the controller adds the two
      // EP0 halves, giving physical indices 0..NBPHYSEP+1.
      physical_index = endpoint.physical_index();
      if (physical_index >= USB_DEV0_NBPHYSEP + 2) begin
        `uvm_fatal("USB_CFG", $sformatf("%s exceeds the DEV0 physical endpoint count of %0d (NBPHYSEP=%0d plus EP0 OUT/IN)", endpoint.convert2string(), USB_DEV0_NBPHYSEP + 2, USB_DEV0_NBPHYSEP))
      end
      if (physical_index_used.exists(physical_index)) begin
        `uvm_fatal("USB_CFG", $sformatf("%s duplicates an endpoint already claiming physical index %0d", endpoint.convert2string(), physical_index))
      end
      physical_index_used[physical_index] = 1'b1;
    end
  endfunction

  // Require one EP0 direction object to describe exactly that direction.
  protected function void validate_control_endpoint_cfg(usb_endpoint_cfg endpoint, usb_direction_e direction);
    string label;

    label = (direction == USB_DIRECTION_IN) ? "ep0_in_cfg" : "ep0_out_cfg";
    if (endpoint == null) begin
      `uvm_fatal("USB_CFG", $sformatf("%s is null; the test must call build_endpoint_cfgs() or build_control_endpoint_cfgs()", label))
    end
    if (endpoint.ep_number != 0 || endpoint.direction != direction || endpoint.transfer_type != USB_TRANSFER_TYPE_CONTROL) begin
      `uvm_fatal("USB_CFG", $sformatf("%s must be EP0 %s CONTROL but is %s", label, (direction == USB_DIRECTION_IN) ? "IN" : "OUT", endpoint.convert2string()))
    end
    if (endpoint.max_packet_size == 0) begin
      `uvm_fatal("USB_CFG", $sformatf("%s has a zero maximum packet size", endpoint.convert2string()))
    end
  endfunction

  // Record each endpoint's VIP anchor: the control endpoint at
  // CONTROL_ANCHOR_INDEX, then the generic endpoints in list order.
  // usb_vip_cfg_builder places each endpoint at exactly this anchor, so the
  // VIP array and the recorded index cannot disagree.
  function void assign_anchor_indices();
    ep0_out_cfg.anchor_index = CONTROL_ANCHOR_INDEX;
    ep0_out_cfg.anchor_index_valid = 1'b1;
    ep0_in_cfg.anchor_index = CONTROL_ANCHOR_INDEX;
    ep0_in_cfg.anchor_index_valid = 1'b1;
    foreach (endpoint_cfgs[index]) begin
      endpoint_cfgs[index].anchor_index = CONTROL_ANCHOR_INDEX + 1 + index;
      endpoint_cfgs[index].anchor_index_valid = 1'b1;
    end
  endfunction

  // Size of the DEV0 endpoint list: two 4-byte words per physical endpoint,
  // counting the two EP0 halves that NBPHYSEP excludes.
  function int unsigned endpoint_list_bytes();
    return (USB_DEV0_NBPHYSEP + 2) * 8;
  endfunction

  // Return the endpoint matching a protocol identity, or null when the bench
  // is not advertising it. EP0 resolves to its direction object, so callers
  // never special-case the control endpoint.
  function usb_endpoint_cfg find_endpoint(int unsigned ep_number, usb_direction_e direction);
    if (ep_number == 0) begin
      return (direction == USB_DIRECTION_IN) ? ep0_in_cfg : ep0_out_cfg;
    end
    foreach (endpoint_cfgs[index]) begin
      if (endpoint_cfgs[index].ep_number == ep_number && endpoint_cfgs[index].direction == direction) begin
        return endpoint_cfgs[index];
      end
    end
    return null;
  endfunction

  // Checked lookup for sequences. Failing here names the requested endpoint
  // and lists what the bench does advertise, so a mismatch is diagnosable
  // without reading the configuration source.
  function usb_endpoint_cfg get_endpoint(int unsigned ep_number, usb_direction_e direction);
    usb_endpoint_cfg endpoint;

    endpoint = find_endpoint(ep_number, direction);
    if (endpoint == null) begin
      `uvm_fatal("USB_CFG", $sformatf("EP%0d %s is not an advertised endpoint. Advertised endpoints: %s", ep_number, (direction == USB_DIRECTION_IN) ? "IN" : "OUT", describe_endpoint_cfgs()))
    end
    return endpoint;
  endfunction

  function string describe_endpoint_cfgs();
    string description;

    description = {(ep0_out_cfg == null) ? "EP0 OUT unset" : ep0_out_cfg.convert2string(), ", ", (ep0_in_cfg == null) ? "EP0 IN unset" : ep0_in_cfg.convert2string()};
    foreach (endpoint_cfgs[index]) begin
      description = {description, ", ", (endpoint_cfgs[index] == null) ? "null" : endpoint_cfgs[index].convert2string()};
    end
    return description;
  endfunction

  // ---------------------------------------------------------------------------
  // uvm_object methods
  // ---------------------------------------------------------------------------

  // Deep copy: endpoint objects are cloned so the copy can be edited without
  // affecting the original.
  virtual function void do_copy(uvm_object rhs);
    usb_env_cfg rhs_cfg;

    super.do_copy(rhs);
    if (!$cast(rhs_cfg, rhs)) begin
      `uvm_fatal("USB_CFG", "do_copy source is not a usb_env_cfg")
    end
    ep0_out_cfg = clone_endpoint(rhs_cfg.ep0_out_cfg);
    ep0_in_cfg = clone_endpoint(rhs_cfg.ep0_in_cfg);
    endpoint_cfgs.delete();
    foreach (rhs_cfg.endpoint_cfgs[index]) begin
      endpoint_cfgs.push_back(clone_endpoint(rhs_cfg.endpoint_cfgs[index]));
    end
    axi_delay_random = rhs_cfg.axi_delay_random;
    device_address = rhs_cfg.device_address;
    endpoint_list_base = rhs_cfg.endpoint_list_base;
    reset_timeout = rhs_cfg.reset_timeout;
    transfer_timeout = rhs_cfg.transfer_timeout;
    vbus_timeout = rhs_cfg.vbus_timeout;
    link_timeout = rhs_cfg.link_timeout;
    control_transfer_timeout = rhs_cfg.control_transfer_timeout;
  endfunction

  protected static function usb_endpoint_cfg clone_endpoint(usb_endpoint_cfg endpoint);
    usb_endpoint_cfg copy;

    if (endpoint == null) begin
      return null;
    end
    if (!$cast(copy, endpoint.clone())) begin
      `uvm_fatal("USB_CFG", "Unable to clone an endpoint configuration")
    end
    return copy;
  endfunction

  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    usb_env_cfg rhs_cfg;

    if (!$cast(rhs_cfg, rhs)) begin
      return 1'b0;
    end
    if (!super.do_compare(rhs, comparer) ||
        !compare_endpoint(ep0_out_cfg, rhs_cfg.ep0_out_cfg, comparer) ||
        !compare_endpoint(ep0_in_cfg, rhs_cfg.ep0_in_cfg, comparer) ||
        endpoint_cfgs.size() != rhs_cfg.endpoint_cfgs.size() ||
        axi_delay_random != rhs_cfg.axi_delay_random ||
        device_address != rhs_cfg.device_address ||
        endpoint_list_base !== rhs_cfg.endpoint_list_base ||
        reset_timeout != rhs_cfg.reset_timeout ||
        transfer_timeout != rhs_cfg.transfer_timeout ||
        vbus_timeout != rhs_cfg.vbus_timeout ||
        link_timeout != rhs_cfg.link_timeout ||
        control_transfer_timeout != rhs_cfg.control_transfer_timeout) begin
      return 1'b0;
    end
    foreach (endpoint_cfgs[index]) begin
      if (!compare_endpoint(endpoint_cfgs[index], rhs_cfg.endpoint_cfgs[index], comparer)) begin
        return 1'b0;
      end
    end
    return 1'b1;
  endfunction

  protected static function bit compare_endpoint(usb_endpoint_cfg lhs, usb_endpoint_cfg rhs, uvm_comparer comparer);
    if (lhs == null || rhs == null) begin
      return lhs == rhs;
    end
    return lhs.compare(rhs, comparer);
  endfunction

  virtual function string convert2string();
    return $sformatf(
      "axi_delay_random=%0b device_address=%0d endpoint_list_base=0x%08h reset_timeout=%0t transfer_timeout=%0t vbus_timeout=%0t link_timeout=%0t control_transfer_timeout=%0t endpoints: %s",
      axi_delay_random,
      device_address,
      endpoint_list_base,
      reset_timeout,
      transfer_timeout,
      vbus_timeout,
      link_timeout,
      control_transfer_timeout,
      describe_endpoint_cfgs()
    );
  endfunction

  virtual function void do_print(uvm_printer printer);
    super.do_print(printer);
    printer.print_int("axi_delay_random", axi_delay_random, 1, UVM_BIN);
    printer.print_int("device_address", device_address, $bits(device_address), UVM_DEC);
    printer.print_int("endpoint_list_base", endpoint_list_base, $bits(endpoint_list_base), UVM_HEX);
    printer.print_time("reset_timeout", reset_timeout);
    printer.print_time("transfer_timeout", transfer_timeout);
    printer.print_time("vbus_timeout", vbus_timeout);
    printer.print_time("link_timeout", link_timeout);
    printer.print_time("control_transfer_timeout", control_transfer_timeout);
    printer.print_object("ep0_out_cfg", ep0_out_cfg);
    printer.print_object("ep0_in_cfg", ep0_in_cfg);
    foreach (endpoint_cfgs[index]) begin
      printer.print_object($sformatf("endpoint_cfgs[%0d]", index), endpoint_cfgs[index]);
    end
  endfunction
endclass
