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
// Bridges one Avery AXI manager interface to the parameterized AXI interface
// used by the USB wrapper. 

`include "uvm_macros.svh"

module usb_axi_manager_connection #(
  parameter string MANAGER_NAME = "unnamed"
) (
  input logic clk,
  input logic rst_n,
  aaxi_intf manager_vif,
  axi_if axi_bus
);
  import uvm_pkg::*;
  import aaxi_pkg::*;
  import usb_tb_pkg::*;

  // Write-address channel. Avery represents AWLOCK as a vector while the
  // parameterized AXI4 interface uses the protocol's scalar lock signal.
  assign axi_bus.awaddr = manager_vif.AWADDR;
  assign axi_bus.awid = manager_vif.AWID;
  assign axi_bus.awlen = manager_vif.AWLEN;
  assign axi_bus.awsize = manager_vif.AWSIZE;
  assign axi_bus.awburst = manager_vif.AWBURST;
  assign axi_bus.awlock = manager_vif.AWLOCK[0];
  assign axi_bus.awcache = manager_vif.AWCACHE;
  assign axi_bus.awprot = manager_vif.AWPROT;
  assign axi_bus.awqos = manager_vif.AWQOS;
  assign axi_bus.awregion = manager_vif.AWREGION;
  assign axi_bus.awuser = manager_vif.AWUSER;
  assign axi_bus.awvalid = manager_vif.AWVALID;
  assign manager_vif.AWREADY = axi_bus.awready;

  // Write-data channel.
  assign axi_bus.wdata = manager_vif.WDATA;
  assign axi_bus.wstrb = manager_vif.WSTRB;
  assign axi_bus.wlast = manager_vif.WLAST;
  assign axi_bus.wuser = manager_vif.WUSER;
  assign axi_bus.wvalid = manager_vif.WVALID;
  assign manager_vif.WREADY = axi_bus.wready;

  // Write-response channel.
  assign manager_vif.BID = axi_bus.bid;
  assign manager_vif.BRESP = axi_bus.bresp;
  assign manager_vif.BUSER = axi_bus.buser;
  assign manager_vif.BVALID = axi_bus.bvalid;
  assign axi_bus.bready = manager_vif.BREADY;

  // Read-address channel. ARLOCK has the same Avery-to-AXI4 width conversion.
  assign axi_bus.araddr = manager_vif.ARADDR;
  assign axi_bus.arid = manager_vif.ARID;
  assign axi_bus.arlen = manager_vif.ARLEN;
  assign axi_bus.arsize = manager_vif.ARSIZE;
  assign axi_bus.arburst = manager_vif.ARBURST;
  assign axi_bus.arlock = manager_vif.ARLOCK[0];
  assign axi_bus.arcache = manager_vif.ARCACHE;
  assign axi_bus.arprot = manager_vif.ARPROT;
  assign axi_bus.arqos = manager_vif.ARQOS;
  assign axi_bus.arregion = manager_vif.ARREGION;
  assign axi_bus.aruser = manager_vif.ARUSER;
  assign axi_bus.arvalid = manager_vif.ARVALID;
  assign manager_vif.ARREADY = axi_bus.arready;

  // Read-response channel.
  assign manager_vif.RID = axi_bus.rid;
  assign manager_vif.RDATA = axi_bus.rdata;
  assign manager_vif.RRESP = axi_bus.rresp;
  assign manager_vif.RLAST = axi_bus.rlast;
  assign manager_vif.RUSER = axi_bus.ruser;
  assign manager_vif.RVALID = axi_bus.rvalid;
  assign axi_bus.rready = manager_vif.RREADY;

  // AXI low-power handshaking is not modeled by the USB wrapper.
  assign manager_vif.CACTIVE_s = 1'b0;
  assign manager_vif.CSYSACK_s = 1'b0;

  aaxi_monitor_wrapper #(
    .VER("AXI4"),
    .ID_WIDTH(USB_TB_AXI_ID_WIDTH),
    .BUS_DATA_WIDTH(USB_AXI_DATA_WIDTH),
    .ADDR_WIDTH(AAXI_ADDR_WIDTH),
    .USER_SUPPORT(5'b11111)
  ) protocol_monitor (
    manager_vif
  );

  // Detect invalid subordinate responses before they can be masked by a test.
  read_response_known: assert property (@(posedge clk) disable iff (!rst_n)
    manager_vif.RVALID |->
      !$isunknown({
        manager_vif.RDATA,
        manager_vif.RRESP,
        manager_vif.RID,
        manager_vif.RLAST,
        manager_vif.RUSER
      }))
    else `uvm_error("USB_AXI_X", $sformatf("%s read response contains X/Z", MANAGER_NAME))

  write_response_known: assert property (@(posedge clk) disable iff (!rst_n)
    manager_vif.BVALID |->
      !$isunknown({
        manager_vif.BRESP,
        manager_vif.BID,
        manager_vif.BUSER
      }))
    else `uvm_error("USB_AXI_X", $sformatf("%s write response contains X/Z", MANAGER_NAME))

  read_request_user_known: assert property (@(posedge clk) disable iff (!rst_n)
    manager_vif.ARVALID |-> !$isunknown(manager_vif.ARUSER))
    else `uvm_error("USB_AXI_X", $sformatf("%s read request USER contains X/Z", MANAGER_NAME))

  write_request_user_known: assert property (@(posedge clk) disable iff (!rst_n)
    manager_vif.AWVALID |-> !$isunknown(manager_vif.AWUSER))
    else `uvm_error("USB_AXI_X", $sformatf("%s write address USER contains X/Z", MANAGER_NAME))

  write_data_user_known: assert property (@(posedge clk) disable iff (!rst_n)
    manager_vif.WVALID |-> !$isunknown(manager_vif.WUSER))
    else `uvm_error("USB_AXI_X", $sformatf("%s write data USER contains X/Z", MANAGER_NAME))

endmodule
