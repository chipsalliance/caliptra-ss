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

class usb_ocp_base_descriptors extends uvm_object;
  `uvm_object_utils(usb_ocp_base_descriptors)
  typedef logic [7:0] bytes_t[$];

  // Firmware capability contract: docs/usb2_streaming_boot_spec/README.md,
  // Section 3.5 specifies 64-byte OCP read/write limits. This is not derived
  // from RTL/RAL or from the independently specified EP0 MaxPacket size.
  localparam logic [15:0] OCP_FIRMWARE_MAX_TRANSFER_BYTES = 16'd64;

  function new(string name = "usb_ocp_base_descriptors");
    super.new(name);
  endfunction

  // Test-owned firmware descriptors, independent of any DUT readback.
  // USB 2.0 9.6; OCP Recovery 1.1 8.5.2-8.5.4. No EPN is advertised.
  static function bytes_t ocp_prepare_descriptor(int device, logic [15:0] value);
    bytes_t data;
    string label;
    case (value[15:8])
      1: begin
        data = '{18,1,8'h00,8'h02,0,0,0,64,
                 8'h09,8'h12,8'(device),8'hca,0,1,0,0,0,1};
      end
      2: begin
        if (device == 1)
          data = '{9,2,28,0,1,1,0,8'h80,50,
                   9,4,0,0,0,8'hef,8'h08,8'h01,1,
                   OCP_USB_FUNC_DESC_LEN,OCP_USB_FUNC_DESC_TYPE,
                   OCP_USB_FUNC_DESC_SUBTYPE,0,
                   OCP_FIRMWARE_MAX_TRANSFER_BYTES[7:0],
                   OCP_FIRMWARE_MAX_TRANSFER_BYTES[15:8],
                   OCP_FIRMWARE_MAX_TRANSFER_BYTES[7:0],
                   OCP_FIRMWARE_MAX_TRANSFER_BYTES[15:8],
                   OCP_USB_BCD_VERSION_1P1[7:0],
                   OCP_USB_BCD_VERSION_1P1[15:8]};
        else
          data = '{9,2,18,0,1,1,0,8'h80,50,9,4,0,0,0,8'hff,0,0,0};
      end
      3: begin
        if (value[7:0] == 0) data = '{4,3,9,4};
        else if (device == 1 && value[7:0] == 1) begin
          label = "OCP Secure Firmware Recovery";
          data.push_back(2 + label.len()*2);
          data.push_back(3);
          for (int i = 0; i < label.len(); i++) begin
            data.push_back(label.getc(i));
            data.push_back(0);
          end
        end
      end
      default: begin end
    endcase
    return data;
  endfunction
endclass
