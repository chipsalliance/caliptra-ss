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
      wire compound_conn_chk``compound_sig = `CPTRA_SS_TOP_PATH.usb_core_i.u_hub_compound.compound_sig;\
      \
      always_comb begin \
        if(waive_chk_at_sim_begin == 0) begin \
          CHK_``sig_name``_UNKNOWN : assert($isunknown(top_sig) == 0) else \
            $error($sformatf("[caliptra_ss_usb_sva] %s is unknown", `"sig_name`")); \
          CHK_``sig_name``_COMPOUND : assert (top_sig === compound_conn_chk``compound_sig) \
            else $error($sformatf("[caliptra_ss_usb_sva] %s value mismatch between top(%b) and compound value(%b)", \
                                    `"sig_name`" , top_sig, compound_conn_chk``compound_sig)); \
        end \
      end

  `define COMPOUND_TIE_INPUT(compound_sig, tie_val, sig_name) \
      wire compound_tie_chk_``compound_sig = `CPTRA_SS_TOP_PATH.usb_core_i.u_hub_compound.compound_sig;\
      \
      always_comb begin \
        if(waive_chk_at_sim_begin == 0) begin \
          $display($sformatf("[caliptra_ss_usb_sva] checking the tie value of %s", `"sig_name`")); \
          CHK_``sig_name``_TIE : assert (tie_val === compound_tie_chk_``compound_sig) \
            else $error($sformatf("[caliptra_ss_usb_sva] %s not tie to %b", `"sig_name`" , tie_val)); \
        end \
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

  `COMPOUND_TIE_INPUT(USB_self_powered,1, SELF_POWERED)
  `COMPOUND_TIE_INPUT(sys_donotwakeup_n, 1, DONOT_WAKEUP)
  `COMPOUND_TIE_INPUT(sys_dev_wakeup_n, 1, DEV_WAKEUP_N)
  `COMPOUND_TIE_INPUT(USB_EnableHub, 0, ENABLE_HUB)

  `undef COMPOUND_TIE_INPUT
  `undef TOP_TO_COMPOUND_CONN
endmodule

