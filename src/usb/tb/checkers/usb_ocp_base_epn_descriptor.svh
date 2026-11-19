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

// USB 2.0 9.6.6/Table 9-13, 5.6.3, 5.8.3. This parser consumes actual
// GET_DESCRIPTOR(configuration) bytes and has no firmware-profile handle.
class usb_ocp_base_epn_descriptor extends uvm_object;
  `uvm_object_utils(usb_ocp_base_epn_descriptor)
  typedef logic [7:0] bytes_t[$];
  usb_endpoint_cfg endpoints[2];
  logic [7:0] configuration;
  logic [7:0] interface_number;
  logic [7:0] alternate;
  bit full_speed;

  function new(string name = "usb_ocp_base_epn_descriptor");
    super.new(name);
  endfunction

  function int ocp_get_period(usb_endpoint_cfg endpoint);
    if (endpoint == null)
      `uvm_fatal("OCP_EPN_DESCRIPTOR", "Missing discovered endpoint for period")
    // USB2 9.6.6: linear FS interrupt, exponential FS ISO/HS periodic.
    if (full_speed && endpoint.transfer_type == USB_TRANSFER_TYPE_INTERRUPT)
      return endpoint.interval;
    return 1 << (endpoint.interval-1);
  endfunction

  function void ocp_check_parse(bytes_t data);
    int pos;
    int iface;
    int alt;
    int declared;
    int count;
    int groups;
    int dir;
    int packet_size;
    int interval;
    usb_transfer_type_e transfer_type;
    usb_endpoint_cfg pair[2];
    logic default_seen[logic [7:0]];
    logic zero_bandwidth[logic [7:0]];
    if (data.size() < 9 || data[0] !== 9 || data[1] !== 2 ||
        {data[3],data[2]} !== data.size() || data[5] === 0)
      `uvm_fatal("OCP_EPN_DESCRIPTOR", "Malformed configuration header")
    foreach (data[i])
      if ($isunknown(data[i]))
        `uvm_fatal("OCP_EPN_DESCRIPTOR", "Unknown descriptor byte")
    configuration = data[5];
    pos = 9;
    iface = -1;
    alt = -1;
    declared = 0;
    count = 0;
    groups = 0;
    pair = '{default:null};
    while (pos <= data.size()) begin
      if (pos != data.size() && (pos+2 > data.size() ||
          data[pos] < 2 || pos+data[pos] > data.size()))
        `uvm_fatal("OCP_EPN_DESCRIPTOR", "Descriptor crosses configuration boundary")
      if (pos == data.size() || data[pos+1] == 4) begin
        if (iface >= 0 && count != declared)
          `uvm_fatal("OCP_EPN_DESCRIPTOR", "Interface endpoint count mismatch")
        if (count != 0) begin
          if (count != 2 || pair[0] == null || pair[1] == null ||
              pair[0].transfer_type != pair[1].transfer_type)
            `uvm_fatal("OCP_EPN_DESCRIPTOR", "Require one unique IN/OUT pair")
          groups++;
          endpoints = pair;
          interface_number = 8'(iface);
          alternate = 8'(alt);
        end
        if (pos == data.size()) break;
      end
      if (pos+2 > data.size() || data[pos] < 2 ||
          pos+data[pos] > data.size())
        `uvm_fatal("OCP_EPN_DESCRIPTOR", "Descriptor crosses configuration boundary")
      case (data[pos+1])
        4: begin
          if (data[pos] !== 9)
            `uvm_fatal("OCP_EPN_DESCRIPTOR", "Malformed interface")
          iface = data[pos+2];
          alt = data[pos+3];
          declared = data[pos+4];
          count = 0;
          pair = '{default:null};
          if (alt == 0) begin
            if (default_seen.exists(8'(iface)))
              `uvm_fatal("OCP_EPN_DESCRIPTOR", "Duplicate default interface")
            default_seen[8'(iface)] = 1;
            zero_bandwidth[8'(iface)] = (declared == 0);
          end
        end
        5: begin
          if (iface < 0 || data[pos] !== 7 || data[pos+2][6:4] !== 0 ||
              data[pos+2][3:0] === 0 || data[pos+5][7:3] !== 0)
            `uvm_fatal("OCP_EPN_DESCRIPTOR", "Invalid endpoint address/packet encoding")
          dir = data[pos+2][7];
          if (pair[dir] != null)
            `uvm_fatal("OCP_EPN_DESCRIPTOR", "Duplicate endpoint direction")
          packet_size = {data[pos+5][2:0],data[pos+4]};
          interval = data[pos+6];
          case (data[pos+3][1:0])
            2: begin
              transfer_type = USB_TRANSFER_TYPE_BULK;
              if ((!full_speed && packet_size != 512) ||
                  (full_speed && !(packet_size inside {8,16,32,64})) ||
                  data[pos+3][7:2] !== 0 || alt != 0)
                `uvm_fatal("OCP_EPN_DESCRIPTOR", "Invalid speed-specific bulk endpoint")
            end
            3: begin
              transfer_type = USB_TRANSFER_TYPE_INTERRUPT;
              if (data[pos+3][7:2] !== 0 || alt != 0)
                `uvm_fatal("OCP_EPN_DESCRIPTOR", "Invalid interrupt attributes/alternate")
            end
            1: begin
              transfer_type = USB_TRANSFER_TYPE_ISOCHRONOUS;
              if (data[pos+3][7:6] !== 0 || alt == 0)
                `uvm_fatal("OCP_EPN_DESCRIPTOR", "ISO bandwidth in default alternate")
            end
            default: `uvm_fatal("OCP_EPN_DESCRIPTOR", "Noncontrol endpoint has CONTROL type")
          endcase
          if (packet_size < 1 || packet_size > 1024 ||
              (full_speed && transfer_type == USB_TRANSFER_TYPE_INTERRUPT && packet_size > 64) ||
              (full_speed && transfer_type == USB_TRANSFER_TYPE_ISOCHRONOUS && packet_size > 1023) ||
              (transfer_type != USB_TRANSFER_TYPE_BULK &&
               (interval < 1 || interval >
                 ((full_speed && transfer_type == USB_TRANSFER_TYPE_INTERRUPT) ? 255 : 16))))
            `uvm_fatal("OCP_EPN_DESCRIPTOR", "Illegal speed-specific size or periodic interval")
          pair[dir] = usb_endpoint_cfg::create_endpoint("discovered_epn",
            data[pos+2][3:0],dir ? USB_DIRECTION_IN : USB_DIRECTION_OUT,
            transfer_type,packet_size,interval);
          count++;
        end
        default: begin end
      endcase
      pos += data[pos];
    end
    if (groups != 1 || default_seen.num() != data[4] ||
        !default_seen.exists(interface_number) ||
        (endpoints[0].transfer_type == USB_TRANSFER_TYPE_ISOCHRONOUS &&
         !zero_bandwidth[interface_number]))
      `uvm_fatal("OCP_EPN_DESCRIPTOR", "Missing unique pair/zero-bandwidth ISO default")
  endfunction
endclass
