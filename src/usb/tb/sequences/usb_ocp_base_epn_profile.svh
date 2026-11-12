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

// Test-owned firmware contract. The host must discover identity and geometry
// from USB descriptors, not consult this object for endpoint configuration.
class usb_ocp_base_epn_profile extends uvm_object;
  `uvm_object_utils(usb_ocp_base_epn_profile)
  typedef logic [7:0] bytes_t[$];
  int unsigned device = 1;
  int unsigned data_tag;
  bit full_speed;
  usb_transfer_type_e transfer_type = USB_TRANSFER_TYPE_BULK;
  // Test data indexed by direction (OUT=0, IN=1), then read/write phase.
  rand int unsigned payload_lengths[2][2] = '{default:'{default:0}};
  bit payload_lengths_selected;

  function new(string name = "usb_ocp_base_epn_profile");
    super.new(name);
  endfunction

  static function usb_transfer_type_e ocp_prepare_selected_type();
    string variant;
    usb_transfer_type_e selected_type;
    case ($urandom_range(0,2))
      0: selected_type = USB_TRANSFER_TYPE_BULK;
      1: selected_type = USB_TRANSFER_TYPE_INTERRUPT;
      2: selected_type = USB_TRANSFER_TYPE_ISOCHRONOUS;
    endcase
    if ($value$plusargs("usb_ocp_epn_type=%s",variant))
      case (variant)
        "BULK": selected_type = USB_TRANSFER_TYPE_BULK;
        "INTERRUPT": selected_type = USB_TRANSFER_TYPE_INTERRUPT;
        "ISOCHRONOUS": selected_type = USB_TRANSFER_TYPE_ISOCHRONOUS;
        default: `uvm_fatal("OCP_EPN_PROFILE", "Supported profiles: BULK, INTERRUPT, ISOCHRONOUS")
      endcase
    return selected_type;
  endfunction

  function usb_endpoint_cfg ocp_prepare_endpoint(usb_direction_e direction);
    return usb_endpoint_cfg::create_endpoint("firmware_epn",1,direction,
      transfer_type,ocp_get_max_packet_size(),ocp_get_interval());
  endfunction

  function int ocp_get_max_packet_size();
    // USB2 5.8.3/5.7.3/5.6.3: 64 bytes is legal for all selected FS types.
    return (!full_speed && transfer_type == USB_TRANSFER_TYPE_BULK) ? 512 : 64;
  endfunction

  function int ocp_get_interval();
    // USB2 9.6.6: exercise linear FS interrupt versus exponential FS ISO.
    if (full_speed && transfer_type == USB_TRANSFER_TYPE_INTERRUPT) return 3;
    if (full_speed && transfer_type == USB_TRANSFER_TYPE_ISOCHRONOUS) return 2;
    return 1;
  endfunction

  function void ocp_prepare_payload_lengths();
    int maximum;
    maximum = ocp_get_max_packet_size();
    if (maximum > 64) maximum = 64;
    if (payload_lengths_selected || !(device inside {1,2}) || maximum < 1)
      `uvm_fatal("OCP_EPN_PROFILE", "Payload lengths require a fresh supported device profile")
    // USB2 5.6.3/5.7.3/5.8.3: one packet may equal the endpoint maximum.
    // Keep every interior length reachable while emphasizing DWORD edges.
    if (!this.randomize() with {
          foreach (payload_lengths[dir,phase]) {
            payload_lengths[dir][phase] inside {[1:local::maximum]};
            payload_lengths[dir][phase] dist {
              1 := 8, [2:3] := 4, 4 := 8, 5 := 4, [6:30] := 1,
              31 := 4, 32 := 8, 33 := 4, [34:59] := 1,
              60 := 8, [61:62] := 4, 63 := 8, 64 := 8
            };
          }
        })
      `uvm_fatal("OCP_EPN_PROFILE", "Payload length randomization failed")
    payload_lengths_selected = 1;
    `uvm_info("OCP_EPN_LENGTHS",$sformatf(
      "slot=%0d OUT0=%0d IN0=%0d OUT1=%0d IN1=%0d maximum=%0d",
      device,payload_lengths[0][0],payload_lengths[1][0],
      payload_lengths[0][1],payload_lengths[1][1],maximum),UVM_NONE)
  endfunction

  function int unsigned ocp_get_payload_length(usb_direction_e direction, int phase);
    int dir;
    if (payload_lengths_selected !== 1 ||
        (direction inside {USB_DIRECTION_OUT,USB_DIRECTION_IN}) !== 1 ||
        (phase inside {0,1}) !== 1)
      `uvm_fatal("OCP_EPN_PROFILE", "Missing selected payload length or invalid direction/phase")
    dir = (direction == USB_DIRECTION_IN);
    if ($isunknown(payload_lengths[dir][phase]) ||
        !(payload_lengths[dir][phase] inside {[1:64]}) ||
        payload_lengths[dir][phase] > ocp_get_max_packet_size())
      `uvm_fatal("OCP_EPN_PROFILE", "Selected payload length exceeds legal profile bounds")
    return payload_lengths[dir][phase];
  endfunction

  function bytes_t ocp_prepare_descriptor(int slot, logic [15:0] value);
    bytes_t data;
    bytes_t extension;
    int size;
    int mps;
    logic [7:0] attributes;
    data = usb_ocp_base_descriptors::ocp_prepare_descriptor(slot,value);
    if (slot != device || value[15:8] !== 2) return data;
    // USB 2.0 5.6.3: ISO default alternate has zero bandwidth.
    if (transfer_type == USB_TRANSFER_TYPE_ISOCHRONOUS) begin
      extension = '{9,4,1,0,0,8'hff,0,0,0};
      data = {data,extension};
    end
    extension = '{9,4,1,
      8'(transfer_type == USB_TRANSFER_TYPE_ISOCHRONOUS),2,8'hff,0,0,0};
    data = {data,extension};
    mps = ocp_get_max_packet_size();
    case (transfer_type)
      USB_TRANSFER_TYPE_BULK: attributes = 2;
      USB_TRANSFER_TYPE_INTERRUPT: attributes = 3;
      USB_TRANSFER_TYPE_ISOCHRONOUS: attributes = 1;
      default: `uvm_fatal("OCP_EPN_PROFILE", "Unsupported firmware endpoint type")
    endcase
    extension = '{7,5,8'h01,attributes,8'(mps),8'(mps>>8),8'(ocp_get_interval()),
                  7,5,8'h81,attributes,8'(mps),8'(mps>>8),8'(ocp_get_interval())};
    data = {data,extension};
    size = data.size();
    data[2] = 8'(size);
    data[3] = 8'(size>>8);
    data[4] = 2;
    return data;
  endfunction

  // Direction/phase tags are test data, not DUT or descriptor expectations.
  static function bytes_t ocp_prepare_stream(
      usb_direction_e direction, int phase, int unsigned payload_length,
      int unsigned data_tag = 0);
    bytes_t data;
    if ((phase inside {0,1}) !== 1)
      `uvm_fatal("OCP_EPN_PROFILE", "Only read/write stream phases are defined")
    if ((direction inside {USB_DIRECTION_OUT,USB_DIRECTION_IN}) !== 1 ||
        $isunknown(payload_length) || !(payload_length inside {[1:64]}))
      `uvm_fatal("OCP_EPN_PROFILE", "Missing or invalid one-packet payload length/direction")
    for (int i = 0; i < payload_length; i++)
      data.push_back(8'(i*7 + phase*53 + data_tag +
        ((direction == USB_DIRECTION_IN) ? 8'ha1 : 8'h12)));
    return data;
  endfunction

  static function logic [31:0] ocp_get_buffer(usb_direction_e direction);
    return (direction == USB_DIRECTION_IN) ? 'h400 : 'h200;
  endfunction

  static function logic [10:0] ocp_get_retired_buffer_offset(
      usb_direction_e direction, int phase, int unsigned payload_length);
    bytes_t data;
    data = ocp_prepare_stream(direction,phase,payload_length);
    // Integration Guide 4.2.3, p48: each successful packet advances the
    // address by ceil(packet_bytes/64). This profile uses one packet.
    return 11'((ocp_get_buffer(direction) >> 6) + ((data.size()+63) >> 6));
  endfunction
endclass
