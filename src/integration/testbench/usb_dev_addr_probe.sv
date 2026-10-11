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
// This module exists only to bridge hub-compound signals into the VCS PLI/ACC
// namespace. VHDL internal architecture signals of the compound IP are not
// registered for PLI access at any debug level, so uvm_hdl_read() cannot
// resolve them directly. Compile-time hierarchical references from this
// SystemVerilog module copy them into plain SV variables, which are
// PLI-visible and can be read by the UVM data-check API.
//
// Committed device address
// ------------------------
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
//
// Negotiated link speed (DEVCMDSTAT[23:22] readback)
// --------------------------------------------------
//   - usb_reg_if holds no speed register. Its pie_speed input port is
//     forwarded combinationally into the register readback in
//     usb_reg_if.m.vhdl: "reg_rdata(23 downto 22) <= pie_speed" for the
//     DEVCMDSTAT address (reg_raddr = "0000"). Probing the port therefore
//     observes exactly what firmware reads back from DEVCMDSTAT.Speed.
//   - Encoding from usb_subcmp_pkg.p.vhdl: FULL_SPEED = "01",
//     HIGH_SPEED = "10".
//   - IMPORTANT: speed is not a per-device quantity in this IP. The compound
//     structure derives one net
//     ("pie_speed <= FULL_SPEED when pie_devicespeed = '0' else HIGH_SPEED")
//     and maps the same sync_pie_speed onto the pie_speed port of BOTH
//     usb_reg_if_1 (dev0) and usb_reg_if_2 (dev1). There is a single upstream
//     USB link behind the compound hub, hence a single negotiated speed.
//     dev0_speed and dev1_speed below are two views of the same net and can
//     never disagree; both names are kept so a per-device test reads
//     naturally, but no independent coverage is gained from checking both.
//
// CHIP_ID (INFO[31:16]) is NOT probed here
// ----------------------------------------
//   CHIP_ID is built from the usb_reg_if C_MAJOR_REV / C_MINOR_REV VHDL
//   generics ("reg_rdata(31 downto 24) <= C_MAJOR_REV",
//   "reg_rdata(23 downto 16) <= C_MINOR_REV"). VCS rejects a cross-module
//   reference whose target is a VHDL generic:
//     Error-[VHDLXMRE-NS] VHDL generic as target of cross module reference
//     is not supported.
//   so the value cannot be bridged from this module. CHIP_ID is instead
//   checked in firmware by reading the INFO register, which exercises the
//   same readback path the generics feed. See usb_check_chip_id() in
//   src/integration/test_suites/libs/usb/usb.c.
module usb_dev_addr_probe;

  logic [6:0] dev0_dev_addr;
  logic [6:0] dev1_dev_addr;
  logic [6:0] hub_dev_addr;

  logic [1:0] dev0_speed;
  logic [1:0] dev1_speed;

  always_comb dev0_dev_addr = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.usbreg_usbaddress;
  always_comb dev1_dev_addr = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.usbreg_usbaddress;
  always_comb hub_dev_addr  = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.usbreg_usbaddress[6:0];

  always_comb dev0_speed = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.pie_speed;
  always_comb dev1_speed = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.pie_speed;

endmodule

// File contains AI-generated response based on internal company sources
