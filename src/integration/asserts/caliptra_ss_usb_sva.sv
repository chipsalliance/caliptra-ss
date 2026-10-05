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

  // Hierarchical shorthands.
  //   - usb_core_i.USB_self_powered           : input pin of the SV AXI
  //     wrapper (ip_xxx_3511_hs_mem_compound_wrapper), fed by the 1'b1
  //     tie-off in caliptra_ss_top.sv.
  //   - usb_core_i.u_hub_compound.USB_self_powered : the same value as seen at
  //     the port of the inner VHDL compound (ip_xxx_3511_hs_mem_compound),
  //     which the wrapper passes straight through. Checking it directly on
  //     the compound instance guards against a broken wrapper connection.
  wire usb_self_powered_pin      = `CPTRA_SS_TOP_PATH.usb_core_i.USB_self_powered;
  wire usb_self_powered_compound = `CPTRA_SS_TOP_PATH.usb_core_i.u_hub_compound.USB_self_powered;

  ////////////////////////////////////////////////////////////////////
  // USB_self_powered tie-off
  //
  // caliptra_ss_top.sv ties the compound core input USB_self_powered to
  // 1'b1. Inside the hub RTL (usb_ep0_hub_descr.m.vhdl) this pin is OR'ed
  // with the HUB_CS[18] firmware override bit to form usb_self_powered,
  // which drives:
  //   - the bmAttributes byte of the configuration descriptor and of the
  //     other-speed configuration descriptor (0xC0 when set, 0x80 when
  //     clear), patched into the EP0 descriptor array at C_ADDR_SP1 /
  //     C_ADDR_SP2 on an edge of usb_self_powered;
  //   - bit0 (Self Powered) of the GET_STATUS(Device) response.
  // If this tie-off is ever changed to 1'b0, the hub reports itself as
  // bus-powered and the host applies the 100/500 mA bus-powered budgeting
  // rules, so the integration value must stay 1.
  ////////////////////////////////////////////////////////////////////
  // USB_self_powered is a static wired tie-off, not a running signal, so
  // there is no value in re-evaluating it on every clock edge. Placing the
  // assertion before the @(usb_self_powered_pin) event control makes the
  // always block evaluate the check once at time 0 (catching a wrong tie-off
  // from the start), then re-check only when the pin actually changes value
  // (which for a correct build never happens after time 0).
  //
  // Two checks are provided: one on the wrapper input pin and one on the
  // inner VHDL compound instance port. They should always agree; keeping
  // both catches either a change to the top-level tie-off or a broken
  // wrapper-to-compound connection.
  always begin
    CHK_SELF_POWERED_WRAPPER: assert (usb_self_powered_pin === 1'b1)
      else $error("[caliptra_ss_usb_sva] USB_self_powered input of usb_core_i is %0b, expected 1'b1 (see the .USB_self_powered tie-off in caliptra_ss_top.sv). Descriptor bmAttributes would report bus-powered (0x80) and GET_STATUS(Device) bit0 would be 0.",
                  usb_self_powered_pin);
    @(usb_self_powered_pin);
  end

  always begin
    CHK_SELF_POWERED_COMPOUND: assert (usb_self_powered_compound === 1'b1)
      else $error("[caliptra_ss_usb_sva] USB_self_powered at usb_core_i.u_hub_compound is %0b, expected 1'b1 (see the .USB_self_powered tie-off in caliptra_ss_top.sv). Descriptor bmAttributes would report bus-powered (0x80) and GET_STATUS(Device) bit0 would be 0.",
                  usb_self_powered_compound);
    @(usb_self_powered_compound);
  end

endmodule

