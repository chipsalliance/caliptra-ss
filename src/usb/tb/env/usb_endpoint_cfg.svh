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
// Configuration object describing one USB endpoint advertised by this bench.
//
// An endpoint configuration is the single place that relates the three
// identities an endpoint carries, so no sequence has to hardcode any of them:
//
//   1. Protocol identity - endpoint number, direction, transfer type, maximum
//      packet size. This is what appears on the wire.
//   2. VIP anchor index - the position this endpoint occupies in the SVT
//      local_device_cfg[0].endpoint_cfg[] array. Host sequences pass this to
//      svt_usb_transfer::fix_anchors(). It is an artifact of the order in
//      which usb_env_cfg lists its endpoints and carries no DUT meaning.
//   3. DUT physical index - the DEV0 controller's physical endpoint number.
//      It selects the endpoint-list entry pair and is the bit position used by
//      EPSKIP, INTEN.EP_INT_EN, and INTSTAT.
//
// The anchor index and the physical index are NOT the same quantity. They
// coincide today only because the default endpoint list happens to be built in
// physical order; permuting the list separates them immediately. Sequences
// must always ask an endpoint configuration rather than assume a literal index.
//
// DEV0 endpoint-list geometry (physical endpoint N):
//
//   entry word 0 -> byte offset N*8 + 0
//   entry word 1 -> byte offset N*8 + 4
//
// Physical endpoint N is derived as (2 * ep_number) + (direction == IN).
// Physical 0/1 are EP0 OUT and EP0 IN; word 1 of the EP0 OUT pair is the SETUP
// entry rather than a second buffer.
//
// Every endpoint direction, including each half of EP0, is one object of this
// class, so lookup and DUT addressing are uniform. The two EP0 objects share
// one VIP anchor because SVT models the control endpoint as a single
// bidirectional entry; usb_env_cfg assigns the anchors.
//
// This object deliberately declares no Synopsys VIP types. It carries only
// bench-local values (usb_direction_e and usb_transfer_type_e from usb_tb_pkg);
// usb_vip_cfg_builder performs the single translation into svt_usb_types
// values so VIP type naming stays confined to one class.

class usb_endpoint_cfg extends uvm_object;
  `uvm_object_utils(usb_endpoint_cfg)

  // ---------------------------------------------------------------------------
  // Protocol identity
  // ---------------------------------------------------------------------------

  int unsigned        ep_number;
  usb_direction_e     direction = USB_DIRECTION_OUT;
  usb_transfer_type_e transfer_type = USB_TRANSFER_TYPE_BULK;
  int unsigned        max_packet_size;
  int unsigned        interval = 1;

  // max_burst_size is only written into the SVT endpoint configuration when it
  // was explicitly requested, so unset entries keep the VIP default.
  int unsigned   max_burst_size;
  bit            max_burst_size_valid;

  // Suppresses the VIP's otherwise mandatory terminating zero-length packet
  // after a max-packet-aligned transfer.
  bit            allow_aligned_transfer_without_zero_length;

  // ---------------------------------------------------------------------------
  // VIP anchor identity, assigned by usb_env_cfg::assign_anchor_indices()
  // ---------------------------------------------------------------------------

  int unsigned   anchor_index;
  bit            anchor_index_valid;

  function new(string name = "usb_endpoint_cfg");
    super.new(name);
  endfunction

  // Build a fully specified endpoint in one expression so endpoint lists
  // read as a table rather than a run of field assignments.
  static function usb_endpoint_cfg create_endpoint(
    string name,
    int unsigned ep_number,
    usb_direction_e direction,
    usb_transfer_type_e transfer_type,
    int unsigned max_packet_size,
    int unsigned interval = 1,
    bit allow_aligned_transfer_without_zero_length = 1'b0,
    int max_burst_size = -1
  );
    usb_endpoint_cfg endpoint;

    endpoint = usb_endpoint_cfg::type_id::create(name);
    endpoint.ep_number = ep_number;
    endpoint.direction = direction;
    endpoint.transfer_type = transfer_type;
    endpoint.max_packet_size = max_packet_size;
    endpoint.interval = interval;
    endpoint.allow_aligned_transfer_without_zero_length = allow_aligned_transfer_without_zero_length;
    if (max_burst_size >= 0) begin
      endpoint.max_burst_size = max_burst_size;
      endpoint.max_burst_size_valid = 1'b1;
    end
    return endpoint;
  endfunction

  // ---------------------------------------------------------------------------
  // DUT physical identity
  // ---------------------------------------------------------------------------

  function int unsigned physical_index();
    return (2 * ep_number) + ((direction == USB_DIRECTION_IN) ? 1 : 0);
  endfunction

  // Byte offset of one of the endpoint's two endpoint-list entry words.
  function logic [31:0] entry_offset(int unsigned buffer_select = 0);
    return 32'((physical_index() * 8) + (buffer_select * 4));
  endfunction

  // Bit position shared by EPSKIP.SKIP, INTEN.EP_INT_EN, and INTSTAT. The
  // generated INTSTAT RAL names per-endpoint fields only through EP5IN and
  // groups the rest as EP_UPPER, so callers use this bit rather than a
  // field lookup.
  function logic [31:0] csr_bit_mask();
    return 32'h1 << physical_index();
  endfunction

  // Short label such as "EP1OUT" for diagnostics.
  function string short_name();
    return $sformatf("EP%0d%s", ep_number, direction_name());
  endfunction

  function string direction_name();
    return (direction == USB_DIRECTION_IN) ? "IN" : "OUT";
  endfunction

  // ---------------------------------------------------------------------------
  // Diagnostics
  // ---------------------------------------------------------------------------

  // One-line identity used by every fatal and progress message so a failure
  // report names the endpoint in all three identity spaces.
  virtual function string convert2string();
    string anchor_text;

    anchor_text = anchor_index_valid ? $sformatf("%0d", anchor_index) : "unassigned";
    return $sformatf(
      "EP%0d %s %s (anchor=%s phys=%0d entry_offset=0x%03h mps=%0d)",
      ep_number,
      direction_name(),
      transfer_type.name(),
      anchor_text,
      physical_index(),
      entry_offset(),
      max_packet_size
    );
  endfunction

  // ---------------------------------------------------------------------------
  // uvm_object methods
  // ---------------------------------------------------------------------------

  virtual function void do_copy(uvm_object rhs);
    usb_endpoint_cfg rhs_endpoint;

    super.do_copy(rhs);
    if (!$cast(rhs_endpoint, rhs)) begin
      `uvm_fatal("USB_CFG", "do_copy source is not a usb_endpoint_cfg")
    end
    ep_number = rhs_endpoint.ep_number;
    direction = rhs_endpoint.direction;
    transfer_type = rhs_endpoint.transfer_type;
    max_packet_size = rhs_endpoint.max_packet_size;
    interval = rhs_endpoint.interval;
    max_burst_size = rhs_endpoint.max_burst_size;
    max_burst_size_valid = rhs_endpoint.max_burst_size_valid;
    allow_aligned_transfer_without_zero_length = rhs_endpoint.allow_aligned_transfer_without_zero_length;
    anchor_index = rhs_endpoint.anchor_index;
    anchor_index_valid = rhs_endpoint.anchor_index_valid;
  endfunction

  // Compares the protocol identity and VIP options. The anchor index is
  // derived from list position, so it is excluded.
  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    usb_endpoint_cfg rhs_endpoint;

    if (!$cast(rhs_endpoint, rhs)) begin
      return 1'b0;
    end
    return super.do_compare(rhs, comparer) &&
           ep_number == rhs_endpoint.ep_number &&
           direction == rhs_endpoint.direction &&
           transfer_type == rhs_endpoint.transfer_type &&
           max_packet_size == rhs_endpoint.max_packet_size &&
           interval == rhs_endpoint.interval &&
           max_burst_size_valid == rhs_endpoint.max_burst_size_valid &&
           (!max_burst_size_valid || max_burst_size == rhs_endpoint.max_burst_size) &&
           allow_aligned_transfer_without_zero_length == rhs_endpoint.allow_aligned_transfer_without_zero_length;
  endfunction

  virtual function void do_print(uvm_printer printer);
    super.do_print(printer);
    printer.print_int("ep_number", ep_number, 32, UVM_DEC);
    printer.print_string("direction", direction.name());
    printer.print_string("transfer_type", transfer_type.name());
    printer.print_int("max_packet_size", max_packet_size, 32, UVM_DEC);
    printer.print_int("interval", interval, 32, UVM_DEC);
    if (max_burst_size_valid) begin
      printer.print_int("max_burst_size", max_burst_size, 32, UVM_DEC);
    end
    printer.print_int("allow_aligned_transfer_without_zero_length", allow_aligned_transfer_without_zero_length, 1, UVM_BIN);
    if (anchor_index_valid) begin
      printer.print_int("anchor_index", anchor_index, 32, UVM_DEC);
    end
    printer.print_int("physical_index", physical_index(), 32, UVM_DEC);
  endfunction
endclass
