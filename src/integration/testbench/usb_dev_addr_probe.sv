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
// The committed device address (address applied after the SET_ADDRESS status
// stage; the *_tmp shadow is deliberately not probed) is read from the ports
// that carry it, not from internal architecture signals:
//   - Each per-device register interface drives its committed address on its
//     usbreg_usbaddress output port (in usb_reg_if.m.vhdl:
//     "usbreg_usbaddress <= reg_dev_addr").
//   - The compound-level hub address is packed into pie_dev_addr and driven
//     into the PIE instance usbreg_usbaddress input port; the hub address
//     occupies the low 7 bits [6:0] (in the compound structure:
//     "pie_dev_addr(C_NBDEV*7-1 downto 0) <= reg_dev_addr").
//   caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound
//     .usb_reg_if_1.usbreg_usbaddress   -> dev0
//     .usb_reg_if_2.usbreg_usbaddress   -> dev1
//     .usb_pie_1.usbreg_usbaddress[6:0] -> hub
module usb_dev_addr_probe;

  logic [6:0] dev0_dev_addr;
  logic [6:0] dev1_dev_addr;
  logic [6:0] hub_dev_addr;

  always_comb dev0_dev_addr = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.usbreg_usbaddress;
  always_comb dev1_dev_addr = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.usbreg_usbaddress;
  always_comb hub_dev_addr  = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.usbreg_usbaddress[6:0];

endmodule

// File contains AI-generated response based on internal company sources
