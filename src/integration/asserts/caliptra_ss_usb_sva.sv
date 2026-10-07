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

`include "caliptra_ss_top_tb_path_defines.svh"

module caliptra_ss_usb_sva ();

  wire usb_self_powered_pin      = `CPTRA_SS_TOP_PATH.usb_core_i.USB_self_powered;
  wire usb_self_powered_compound = `CPTRA_SS_TOP_PATH.usb_core_i.u_hub_compound.USB_self_powered;
  logic waive_chk_at_sim_begin   = 1;

  initial begin
    waive_chk_at_sim_begin = 1;
    #1us;
    waive_chk_at_sim_begin = 0;
  end

  always begin
    if(waive_chk_at_sim_begin == 0) begin
      CHK_SELF_POWERED_WRAPPER: assert (usb_self_powered_pin === 1'b1)
        else $error("[caliptra_ss_usb_sva] USB_self_powered input of usb_core_i is %0b, expected 1'b1 (see the .USB_self_powered tie-off in caliptra_ss_top.sv). Descriptor bmAttributes would report bus-powered (0x80) and GET_STATUS(Device) bit0 would be 0.",
                    usb_self_powered_pin);
    end
    @(usb_self_powered_pin, waive_chk_at_sim_begin);
  end

  always begin
    if(waive_chk_at_sim_begin == 0) begin
      CHK_SELF_POWERED_COMPOUND: assert (usb_self_powered_compound === 1'b1)
        else $error("[caliptra_ss_usb_sva] USB_self_powered at usb_core_i.u_hub_compound is %0b, expected 1'b1 (see the .USB_self_powered tie-off in caliptra_ss_top.sv). Descriptor bmAttributes would report bus-powered (0x80) and GET_STATUS(Device) bit0 would be 0.",
                    usb_self_powered_compound);
    end
    @(usb_self_powered_compound, waive_chk_at_sim_begin);
  end

endmodule

