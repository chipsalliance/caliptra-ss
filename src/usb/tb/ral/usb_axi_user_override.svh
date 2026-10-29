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
// Per-access request USER value shared by native and RAL AXI traffic.
class usb_axi_user_override extends uvm_object;
  `uvm_object_utils(usb_axi_user_override)

  bit [USB_TB_AXI_USER_WIDTH-1:0] value;

  function new(string name = "usb_axi_user_override");
    super.new(name);
  endfunction

  static function usb_axi_user_override with_value(bit [USB_TB_AXI_USER_WIDTH-1:0] value);
    usb_axi_user_override user_override;

    user_override = usb_axi_user_override::type_id::create("user_override");
    user_override.value = value;
    return user_override;
  endfunction

  static function usb_axi_user_override resolve(uvm_object extension = null);
    usb_axi_user_override user_override;
    bit [USB_TB_AXI_USER_WIDTH-1:0] random_value;

    if (extension != null) begin
      if (!$cast(user_override, extension)) begin
        `uvm_fatal("USB_AXI_USER", "RAL extension is not a usb_axi_user_override")
        return null;
      end
      return user_override;
    end

    if (!std::randomize(random_value)) begin
      `uvm_fatal("USB_AXI_USER", "Unable to randomize request USER")
      return null;
    end
    return with_value(random_value);
  endfunction
endclass
