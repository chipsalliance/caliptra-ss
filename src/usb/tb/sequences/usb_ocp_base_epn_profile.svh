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
      usb_direction_e direction, int phase, int unsigned data_tag = 0);
    bytes_t data;
    int size;
    if (!(phase inside {0,1}))
      `uvm_fatal("OCP_EPN_PROFILE", "Only read/write stream phases are defined")
    size = (phase == 0) ? 31 : 29;
    for (int i = 0; i < size; i++)
      data.push_back(8'(i*7 + phase*53 + data_tag +
        ((direction == USB_DIRECTION_IN) ? 8'ha1 : 8'h12)));
    return data;
  endfunction

  static function logic [31:0] ocp_get_buffer(usb_direction_e direction);
    return (direction == USB_DIRECTION_IN) ? 'h400 : 'h200;
  endfunction

  static function logic [10:0] ocp_get_retired_buffer_offset(
      usb_direction_e direction, int phase);
    bytes_t data;
    data = ocp_prepare_stream(direction,phase);
    // Integration Guide 4.2.3, p48: each successful packet advances the
    // address by ceil(packet_bytes/64). This profile uses one short packet.
    return 11'((ocp_get_buffer(direction) >> 6) + ((data.size()+63) >> 6));
  endfunction
endclass
