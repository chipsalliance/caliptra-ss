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
// Declarative description of one USB endpoint used by this bench.
//
// A profile is the single place that relates the three independent identities
// an endpoint carries, so no sequence has to hardcode any of them:
//
//   1. Protocol identity - endpoint number, direction, transfer type, maximum
//      packet size. This is what appears on the wire.
//   2. VIP anchor index - the position this endpoint occupies in the SVT
//      local_device_cfg[0].endpoint_cfg[] array. Host sequences pass this to
//      svt_usb_transfer::fix_anchors(). It is an artifact of the order in
//      which the profile was built and carries no DUT meaning.
//   3. DUT physical index - the DEV0 controller's physical endpoint number.
//      It selects the endpoint-list entry pair and is the bit position used by
//      EPSKIP, INTEN.EP_INT_EN, and INTSTAT.
//
// The anchor index and the physical index are NOT the same quantity. They
// coincide today only because the default profile happens to be built in
// physical order; permuting the profile separates them immediately. Sequences
// must always ask a profile rather than assume a literal index.
//
// DEV0 endpoint-list geometry (physical endpoint N):
//
//   entry word 0 -> byte offset N*8 + 0
//   entry word 1 -> byte offset N*8 + 4
//
// Physical endpoint N is derived as (2 * ep_number) + (direction == IN).
// Physical 0/1 are the control endpoint's OUT and IN halves; for the control
// endpoint, word 1 of the OUT pair is the SETUP entry rather than a second
// buffer.
//
// This object deliberately declares no Synopsys VIP types. It carries only
// bench-local values; usb_env_cfg::apply_endpoint_profile() performs the single
// translation into svt_usb_types values so VIP type naming stays confined to
// one function.

typedef enum int {
  USB_EP_DIR_OUT,
  USB_EP_DIR_IN
} usb_ep_dir_e;

typedef enum int {
  USB_EP_KIND_CONTROL,
  USB_EP_KIND_BULK,
  USB_EP_KIND_INTERRUPT,
  USB_EP_KIND_ISOCHRONOUS
} usb_ep_kind_e;

class usb_endpoint_profile extends uvm_object;
  `uvm_object_utils(usb_endpoint_profile)

  // ---------------------------------------------------------------------------
  // Protocol identity
  // ---------------------------------------------------------------------------

  int unsigned   ep_number;
  usb_ep_dir_e   direction = USB_EP_DIR_OUT;
  usb_ep_kind_e  ep_kind = USB_EP_KIND_BULK;
  int unsigned   max_packet_size;
  int unsigned   interval = 1;

  // max_burst_size is only written into the SVT endpoint configuration when it
  // was explicitly requested, so unset entries keep the VIP default.
  int unsigned   max_burst_size;
  bit            max_burst_size_valid;

  // Suppresses the VIP's otherwise mandatory terminating zero-length packet
  // after a max-packet-aligned transfer.
  bit            allow_aligned_transfer_without_zero_length;

  // ---------------------------------------------------------------------------
  // VIP anchor identity, assigned by usb_env_cfg when the profile is applied
  // ---------------------------------------------------------------------------

  int unsigned   anchor_index;
  bit            anchor_index_valid;

  function new(string name = "usb_endpoint_profile");
    super.new(name);
  endfunction

  // Build a fully specified endpoint in one expression so profile definitions
  // read as a table rather than a run of field assignments.
  static function usb_endpoint_profile create_endpoint(
    string name,
    int unsigned ep_number,
    usb_ep_dir_e direction,
    usb_ep_kind_e ep_kind,
    int unsigned max_packet_size,
    int unsigned interval = 1,
    bit allow_aligned_transfer_without_zero_length = 1'b0,
    int max_burst_size = -1
  );
    usb_endpoint_profile endpoint;

    endpoint = usb_endpoint_profile::type_id::create(name);
    endpoint.ep_number = ep_number;
    endpoint.direction = direction;
    endpoint.ep_kind = ep_kind;
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

  // Physical endpoint index for an explicit direction. The control endpoint is
  // bidirectional, so callers that need its IN half pass USB_EP_DIR_IN here
  // rather than relying on the profile's nominal direction.
  function int unsigned physical_index_for(usb_ep_dir_e dir);
    return (2 * ep_number) + ((dir == USB_EP_DIR_IN) ? 1 : 0);
  endfunction

  function int unsigned physical_index();
    return physical_index_for(direction);
  endfunction

  // Byte offset of one of the endpoint's two endpoint-list entry words.
  function logic [31:0] entry_offset(int unsigned buffer_select = 0);
    return 32'((physical_index() * 8) + (buffer_select * 4));
  endfunction

  // Bit position shared by EPSKIP.SKIP, INTEN.EP_INT_EN, and INTSTAT. The
  // generated INTSTAT RAL names per-endpoint fields only through EP5IN and
  // groups the rest as EP_UPPER, so callers use this bit rather than a field
  // lookup.
  function logic [31:0] csr_bit_mask();
    return 32'h1 << physical_index();
  endfunction

  // Short label such as "EP1OUT" for diagnostics.
  function string short_name();
    return $sformatf("EP%0d%s", ep_number, direction_name());
  endfunction

  function string direction_name();
    return (direction == USB_EP_DIR_IN) ? "IN" : "OUT";
  endfunction

  // The SVT control endpoint anchor is declared IN regardless of the bench-side
  // direction, matching the VIP's bidirectional control convention.
  function bit svt_direction_is_in();
    return (ep_kind == USB_EP_KIND_CONTROL) || (direction == USB_EP_DIR_IN);
  endfunction

  // Copy of this endpoint bound to one direction. A control endpoint has a
  // single profile entry but two DUT halves, so a lookup for its other half
  // gets a view whose physical index, entry offset, and CSR bit all follow the
  // requested direction. The view keeps the shared anchor identity and is not
  // part of the profile the VIP is configured from.
  function usb_endpoint_profile view_for_direction(usb_ep_dir_e dir);
    usb_endpoint_profile view;

    if (dir == direction) begin
      return this;
    end
    view = usb_endpoint_profile::type_id::create({get_name(), "_", (dir == USB_EP_DIR_IN) ? "in" : "out"});
    view.ep_number = ep_number;
    view.direction = dir;
    view.ep_kind = ep_kind;
    view.max_packet_size = max_packet_size;
    view.interval = interval;
    view.max_burst_size = max_burst_size;
    view.max_burst_size_valid = max_burst_size_valid;
    view.allow_aligned_transfer_without_zero_length = allow_aligned_transfer_without_zero_length;
    view.anchor_index = anchor_index;
    view.anchor_index_valid = anchor_index_valid;
    return view;
  endfunction

  // ---------------------------------------------------------------------------
  // Diagnostics
  // ---------------------------------------------------------------------------

  // One-line identity used by every fatal and progress message so a failure
  // report names the endpoint in all three identity spaces.
  function string describe();
    string anchor_text;

    anchor_text = anchor_index_valid ? $sformatf("%0d", anchor_index) : "unassigned";
    return $sformatf(
      "EP%0d %s %s (anchor=%s phys=%0d entry_offset=0x%03h mps=%0d)",
      ep_number,
      direction_name(),
      ep_kind.name(),
      anchor_text,
      physical_index(),
      entry_offset(),
      max_packet_size
    );
  endfunction
endclass
