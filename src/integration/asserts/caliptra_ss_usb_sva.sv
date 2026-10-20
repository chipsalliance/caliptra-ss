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
  logic waive_chk_at_sim_begin   = 1;

  `define TOP_TO_COMPOUND_CONN(top_sig, compound_sig, sig_name) \
      wire compound_``compound_sig = `CPTRA_SS_TOP_PATH.usb_core_i.u_hub_compound.compound_sig;\
      \
      always begin \
        if(waive_chk_at_sim_begin == 0) begin \
          $display("[caliptra_ss_usb_sva] checking USB_self_powered input of usb_core_i"); \
          CHK_``sig_name``_COMPOUND : assert (top_sig === compound_``compound_sig) \
            else $error($sformatf("[caliptra_ss_usb_sva] %s value mismatch between top(%b) and compound value(%b)", `"sig_name`" , top_sig, compound_``compound_sig)); \
        end \
        @(top_sig, compound_``compound_sig, waive_chk_at_sim_begin);\
      end


  initial begin
    waive_chk_at_sim_begin = 1;
    #1us;
    waive_chk_at_sim_begin = 0;
  end

  always begin
    if(waive_chk_at_sim_begin == 0) begin
      $display("[caliptra_ss_usb_sva] checking USB_self_powered input of usb_core_i");
      CHK_SELF_POWERED_WRAPPER: assert (usb_self_powered_pin === 1'b1)
        else $error("[caliptra_ss_usb_sva] USB_self_powered input of usb_core_i is %0b, expected 1'b1 (see the .USB_self_powered tie-off in caliptra_ss_top.sv). Descriptor bmAttributes would report bus-powered (0x80) and GET_STATUS(Device) bit0 would be 0.",
                    usb_self_powered_pin);
    end
    @(usb_self_powered_pin, waive_chk_at_sim_begin);
  end

  `TOP_TO_COMPOUND_CONN(`CPTRA_SS_TOP_PATH.cptra_ss_usb_self_powered_i, USB_self_powered, SELF_POWERED)

  `TOP_TO_COMPOUND_CONN(`CPTRA_SS_TOP_PATH.cptra_ss_usb_donotwakeup_n_i, sys_donotwakeup_n, DONOT_WAKEUP)

  `TOP_TO_COMPOUND_CONN(`CPTRA_SS_TOP_PATH.cptra_ss_usb_dev_wakeup_n_i, sys_dev_wakeup_n, DEV_WAKEUP_N)

  `TOP_TO_COMPOUND_CONN(`CPTRA_SS_TOP_PATH.cptra_ss_usb_enable_hub_i, USB_EnableHub, ENABLE_HUB)
endmodule

