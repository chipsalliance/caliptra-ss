// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// you may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
`include "uvm_macros.svh"
`include "svt_usb_defines.svi"
`include "svt_usb_if.uvm.svi"

// Standalone UVM harness for the compound USB subsystem. It supplies four
// independent AXI managers, two packet SRAMs, and an SVT UTMI PHY.
// The DUT remains in device mode; unused host, ULPI, wake, and test controls
// are tied to their inactive values.
module usb_top_tb;
  timeunit 1ns;
  timeprecision 1ps;

  import uvm_pkg::*;
  import aaxi_pkg::*;
  import usb_tb_pkg::*;

  // --------------------------------------------------------------------------
  // Configuration and internal signals
  // --------------------------------------------------------------------------
  localparam realtime USB_AXI_CLOCK_PERIOD = 2.5ns;

  // Clock, reset, and global testbench control.
  logic bus_clk = 0;
  logic phy_clk = 0;
  logic bus_reset_n = 0;
  logic phy_clock_locked = 0;

  // UTMI connections between the DUT and the SVT USB VIP.
  logic [7:0] dut_utmi_txdata;
  logic dut_utmi_txvalid;
  logic dut_utmi_reset;
  logic dut_utmi_suspendm;
  logic dut_utmi_xcvrselect;
  logic dut_utmi_termselect;
  logic [1:0] dut_utmi_opmode;
  logic [1:0] usb_dut_vip_xcvrselect;

  // Device 0 packet-memory signals.
  logic [63:0] dev0_memory_read_data;
  logic [63:0] dev0_memory_write_data;
  logic [63:0] dev0_memory_write_mask;
  logic [$clog2(USB_DEV0_RAM_DEPTH)-1:0] dev0_memory_address;
  logic dev0_memory_request;
  logic dev0_memory_write_enable_n;

  // Device 1 packet-memory signals.
  logic [63:0] dev1_memory_read_data;
  logic [63:0] dev1_memory_write_data;
  logic [63:0] dev1_memory_write_mask;
  logic [$clog2(USB_DEV1_RAM_DEPTH)-1:0] dev1_memory_address;
  logic dev1_memory_request;
  logic dev1_memory_write_enable_n;

  // --------------------------------------------------------------------------
  // Testbench interfaces
  // --------------------------------------------------------------------------
  svt_usb_if usb_20_mac_if();

  // Low-power AXI handshaking is outside this focused TB, so each manager
  // permanently requests an active interface and leaves status outputs open.
  aaxi_intf combo_manager_vif (
    .ACLK(bus_clk),
    .ARESETn(bus_reset_n),
    .CACTIVE(),
    .CSYSREQ(1'b1),
    .CSYSACK()
  );
  aaxi_intf dev0_memory_manager_vif (
    .ACLK(bus_clk),
    .ARESETn(bus_reset_n),
    .CACTIVE(),
    .CSYSREQ(1'b1),
    .CSYSACK()
  );
  aaxi_intf dev1_csr_manager_vif (
    .ACLK(bus_clk),
    .ARESETn(bus_reset_n),
    .CACTIVE(),
    .CSYSREQ(1'b1),
    .CSYSACK()
  );
  aaxi_intf dev1_memory_manager_vif (
    .ACLK(bus_clk),
    .ARESETn(bus_reset_n),
    .CACTIVE(),
    .CSYSREQ(1'b1),
    .CSYSACK()
  );

  // Parameterized AXI interfaces connect the managers to the DUT.
  axi_if #(
    .AW(USB_AXI_ADDR_WIDTH),
    .DW(USB_AXI_DATA_WIDTH),
    .IW(USB_TB_AXI_ID_WIDTH),
    .UW(USB_TB_AXI_USER_WIDTH)
  ) combo_axi_bus (
    .clk(bus_clk),
    .rst_n(bus_reset_n)
  );
  axi_if #(
    .AW(USB_AXI_ADDR_WIDTH),
    .DW(USB_AXI_DATA_WIDTH),
    .IW(USB_TB_AXI_ID_WIDTH),
    .UW(USB_TB_AXI_USER_WIDTH)
  ) dev0_memory_axi_bus (
    .clk(bus_clk),
    .rst_n(bus_reset_n)
  );
  axi_if #(
    .AW(USB_AXI_ADDR_WIDTH),
    .DW(USB_AXI_DATA_WIDTH),
    .IW(USB_TB_AXI_ID_WIDTH),
    .UW(USB_TB_AXI_USER_WIDTH)
  ) dev1_csr_axi_bus (
    .clk(bus_clk),
    .rst_n(bus_reset_n)
  );
  axi_if #(
    .AW(USB_AXI_ADDR_WIDTH),
    .DW(USB_AXI_DATA_WIDTH),
    .IW(USB_TB_AXI_ID_WIDTH),
    .UW(USB_TB_AXI_USER_WIDTH)
  ) dev1_memory_axi_bus (
    .clk(bus_clk),
    .rst_n(bus_reset_n)
  );

  // --------------------------------------------------------------------------
  // Testbench infrastructure
  // --------------------------------------------------------------------------
  // Each connection adapts one Avery manager to the DUT's AXI interface.
  usb_axi_manager_connection #(
    .MANAGER_NAME("combo")
  ) combo_axi_connection (
    .clk(bus_clk),
    .rst_n(bus_reset_n),
    .manager_vif(combo_manager_vif),
    .axi_bus(combo_axi_bus)
  );
  usb_axi_manager_connection #(
    .MANAGER_NAME("dev0_memory")
  ) dev0_memory_axi_connection (
    .clk(bus_clk),
    .rst_n(bus_reset_n),
    .manager_vif(dev0_memory_manager_vif),
    .axi_bus(dev0_memory_axi_bus)
  );
  usb_axi_manager_connection #(
    .MANAGER_NAME("dev1_csr")
  ) dev1_csr_axi_connection (
    .clk(bus_clk),
    .rst_n(bus_reset_n),
    .manager_vif(dev1_csr_manager_vif),
    .axi_bus(dev1_csr_axi_bus)
  );
  usb_axi_manager_connection #(
    .MANAGER_NAME("dev1_memory")
  ) dev1_memory_axi_connection (
    .clk(bus_clk),
    .rst_n(bus_reset_n),
    .manager_vif(dev1_memory_manager_vif),
    .axi_bus(dev1_memory_axi_bus)
  );

  // The packet SRAMs adapt active-low write enables and bit-granular masks.
  caliptra_prim_generic_ram_1p #(
    .Width(64),
    .Depth(USB_DEV0_RAM_DEPTH),
    .DataBitsPerMask(1)
  ) dev0_packet_memory (
    .clk_i(bus_clk),
    .req_i(dev0_memory_request),
    .write_i(~dev0_memory_write_enable_n),
    .addr_i(dev0_memory_address),
    .wdata_i(dev0_memory_write_data),
    .wmask_i(dev0_memory_write_mask),
    .rdata_o(dev0_memory_read_data),
    .cfg_i('0)
  );

  caliptra_prim_generic_ram_1p #(
    .Width(64),
    .Depth(USB_DEV1_RAM_DEPTH),
    .DataBitsPerMask(1)
  ) dev1_packet_memory (
    .clk_i(bus_clk),
    .req_i(dev1_memory_request),
    .write_i(~dev1_memory_write_enable_n),
    .addr_i(dev1_memory_address),
    .wdata_i(dev1_memory_write_data),
    .wmask_i(dev1_memory_write_mask),
    .rdata_o(dev1_memory_read_data),
    .cfg_i('0)
  );

  // --------------------------------------------------------------------------
  // Device under test
  // --------------------------------------------------------------------------
  // Keep the DUT connected to the SVT UTMI interface in both scenarios;
  // register-only tests use the same wiring, not a separate idle-PHY fallback.
  ip_xxx_3511_hs_mem_compound_wrapper #(
    .C_HUB_FIFO_SIZE(USB_HUB_FIFO_SIZE),
    .C_DEV0_RAM_ADDRWIDTH($clog2(USB_DEV0_RAM_DEPTH)),
    .C_DEV1_RAM_ADDRWIDTH($clog2(USB_DEV1_RAM_DEPTH)),
    .C_DEV0_NBPHYSEP(USB_DEV0_NBPHYSEP),
    .C_DEV1_NBPHYSEP(USB_DEV1_NBPHYSEP),
    .C_EPUB(USB_EPUB),
    .C_DAUB(USB_DAUB),
    .C_DALB(USB_DALB),
    .C_SINGLE_BUFFER_SUPPORTED(USB_SINGLE_BUFFER_SUPPORTED),
    .C_DOUBLE_BUFFER_SUPPORTED(USB_DOUBLE_BUFFER_SUPPORTED),
    .C_TOGGLE_REG_READABLE(USB_TOGGLE_REG_READABLE),
    .C_EPFIFO_PAGE(USB_EPFIFO_PAGE),
    .C_DATAFIFO_PAGE(USB_DATAFIFO_PAGE),
    .G_SIM_CHIRP_TIMERS(1)
  ) dut (
    .usb_axi_aclk(bus_clk),
    .usb_axi_aresetn(bus_reset_n),
    .combo_axi_if_w_sub(combo_axi_bus),
    .combo_axi_if_r_sub(combo_axi_bus),
    .dev0_mem_axi_if_w_sub(dev0_memory_axi_bus),
    .dev0_mem_axi_if_r_sub(dev0_memory_axi_bus),
    .dev1_csr_axi_if_w_sub(dev1_csr_axi_bus),
    .dev1_csr_axi_if_r_sub(dev1_csr_axi_bus),
    .dev1_mem_axi_if_w_sub(dev1_memory_axi_bus),
    .dev1_mem_axi_if_r_sub(dev1_memory_axi_bus),
    .dev0_mem_q(dev0_memory_read_data),
    .dev0_mem_d(dev0_memory_write_data),
    .dev0_mem_cs(dev0_memory_request),
    .dev0_mem_a(dev0_memory_address),
    .dev0_mem_web_out(dev0_memory_write_enable_n),
    .dev0_mem_bsel(dev0_memory_write_mask),
    .dev1_mem_q(dev1_memory_read_data),
    .dev1_mem_d(dev1_memory_write_data),
    .dev1_mem_cs(dev1_memory_request),
    .dev1_mem_a(dev1_memory_address),
    .dev1_mem_web_out(dev1_memory_write_enable_n),
    .dev1_mem_bsel(dev1_memory_write_mask),
    .dev0_usb_irq(),
    .dev0_usb_fiq(),
    .dev1_usb_irq(),
    .dev1_usb_fiq(),
    .usb_frametoggle(),
    .payload_available     (),
    .ocp_firmware_activated(),
    // Device-mode VBus/session indications come from SVT.
    .USB_VBus(usb_20_mac_if.utmi_dut_mac_if.VbusValid),
    .vbuscomp_on(),
    .chrg_vbus(),
    .dischrg_vbus(),
    .avalid(1'b0),
    .sessend(usb_20_mac_if.utmi_dut_mac_if.SessEnd),
    .utmi_clk(usb_20_mac_if.utmi_dut_mac_if.CLK),
    .utmi_rxdata(usb_20_mac_if.utmi_dut_mac_if.DataOut[7:0]),
    .utmi_rxvalid(usb_20_mac_if.utmi_dut_mac_if.RXValid),
    .utmi_rxactive(usb_20_mac_if.utmi_dut_mac_if.RXActive),
    .utmi_rxerror(usb_20_mac_if.utmi_dut_mac_if.RXError),
    .utmi_txdata(dut_utmi_txdata),
    .utmi_txvalid(dut_utmi_txvalid),
    .utmi_txready(usb_20_mac_if.utmi_dut_mac_if.TXReady),
    .utmi_reset(dut_utmi_reset),
    .utmi_suspendm(dut_utmi_suspendm),
    .utmi_xcvrselect(dut_utmi_xcvrselect),
    .utmi_termselect(dut_utmi_termselect),
    .utmi_opmode(dut_utmi_opmode),
    .utmi_linestate(usb_20_mac_if.utmi_dut_mac_if.LineState),
    .utmi_vcontrol(),
    .utmi_vcontrolloadm(),
    .utmi_vstatus(8'h00),
    // ULPI is not exercised; all ULPI inputs are held at inactive values.
    .ulpi_clk(phy_clk),
    .ulpi_rxdata(8'h00),
    .ulpi_txdata(),
    .ulpi_txenable(),
    .ulpi_dir(1'b0),
    .ulpi_stp(),
    .ulpi_nxt(1'b0),
    .ulpi_ddr_sel(1'b0),
    .usb_needclk(),
    // System wake/test policy is not modeled by this standalone harness.
    .sys_donotwakeup_n(1'b1),
    .sys_dev_wakeup_n(1'b1),
    .sys_utmi_clkin_lock(phy_clock_locked),
    .USB_EnableHub(1'b0),
    .USB_self_powered(1'b0),
    .testmode(1'b0),
    .async_disable(1'b0)
  );

  // --------------------------------------------------------------------------
  // Clock generation and static USB connectivity
  // --------------------------------------------------------------------------
  // The AXI bus runs at 400 MHz. Keep a free-running reference for the VIP
  // testbench clock; the modeled PHY owns the DUT's suspend-gated UTMI CLK.
  always #(USB_AXI_CLOCK_PERIOD / 2.0) bus_clk = ~bus_clk;
  always #8.333ns phy_clk = ~phy_clk;

  // The compound wrapper exposes device-side UTMI controls. Host pull-downs,
  // 16-bit UTMI, serial mode, and optional low-power controls are unsupported.
  assign usb_20_mac_if.utmi_dut_mac_if.DataIn = dut_utmi_txdata;
  assign usb_20_mac_if.utmi_dut_mac_if.TXValid = dut_utmi_txvalid;
  assign usb_20_mac_if.utmi_dut_mac_if.Reset = dut_utmi_reset;
  assign usb_20_mac_if.utmi_dut_mac_if.SuspendM = dut_utmi_suspendm;
  // The wrapper exposes ordinary SuspendM but no USB LPM sleep controls. This
  // bench does not generate L1 or deep/shallow LPM states, so drive the
  // SVT-only extension pins to fixed known values.
  assign usb_20_mac_if.utmi_dut_mac_if.SleepM = 1'b0;
  assign usb_20_mac_if.utmi_dut_mac_if.L1SuspendM = 1'b0;
  // The DUT has a scalar XcvrSelect output; the SVT interface has two bits.
  assign usb_dut_vip_xcvrselect = {1'b0, dut_utmi_xcvrselect};
  assign usb_20_mac_if.utmi_dut_mac_if.XcvrSelect = usb_dut_vip_xcvrselect;
  assign usb_20_mac_if.utmi_dut_mac_if.TermSelect = dut_utmi_termselect;
  assign usb_20_mac_if.utmi_dut_mac_if.OpMode = dut_utmi_opmode;
  // The DUT is a fixed peripheral, not a downstream-facing host port. Keep
  // its host pull-down controls disabled; the SVT host owns host termination.
  assign usb_20_mac_if.utmi_dut_mac_if.DpPulldown = 1'b0;
  assign usb_20_mac_if.utmi_dut_mac_if.DmPulldown = 1'b0;
  // Model the device full-speed pull-up from the DUT's TermSelect control.
  assign usb_20_mac_if.utmi_dut_mac_if.FsPullup = (dut_utmi_termselect == 1'b1) ? 1'b1 : 1'bz;
  // A high-speed-capable device initially attaches with the FS pull-up before
  // speed negotiation; this DUT never advertises a low-speed attachment.
  assign usb_20_mac_if.utmi_dut_mac_if.LsPullup = 1'b0;
  // The compound wrapper implements the 8-bit UTMI data path only. There is no
  // upper transmit byte to validate, and DataBus16_8 selects 8-bit operation.
  assign usb_20_mac_if.utmi_dut_mac_if.TXValidH = 1'b0;
  assign usb_20_mac_if.utmi_dut_mac_if.DataBus16_8 = 1'b0;
  // DataIn/TXValid above carry normal parallel UTMI traffic. Disable the
  // alternate FS/LS serial path, deassert its active-low output enable, and
  // hold its unused raw data and SE0 controls low.
  assign usb_20_mac_if.utmi_dut_mac_if.Tx_Enable_N = 1'b1;
  assign usb_20_mac_if.utmi_dut_mac_if.Tx_DAT = 1'b0;
  assign usb_20_mac_if.utmi_dut_mac_if.Tx_SE0 = 1'b0;
  assign usb_20_mac_if.utmi_dut_mac_if.FsLsSerialMode = 1'b0;
  // Role selection is fixed to device mode, so the PHY must not sample an OTG
  // ID pin or switch between A-device and B-device behavior.
  assign usb_20_mac_if.utmi_dut_mac_if.IdPullup = 1'b0;
  // The standalone harness models an already powered cable/session and does
  // not exercise OTG VBUS negotiation. Keep the SVT PHY's VBUS drive request
  // asserted for that session and disable charge/discharge pulses.
  assign usb_20_mac_if.utmi_dut_mac_if.DrvVbus = 1'b1;
  assign usb_20_mac_if.utmi_dut_mac_if.ChrgVbus = 1'b0;
  assign usb_20_mac_if.utmi_dut_mac_if.DischrgVbus = 1'b0;
  // These enables apply only to the VIP's raw transmit OpMode. The DUT uses
  // normal encoded UTMI traffic, and the high-byte control is also absent on
  // the selected 8-bit interface.
  assign usb_20_mac_if.utmi_dut_mac_if.TxBitstuffEnable = 1'b0;
  assign usb_20_mac_if.utmi_dut_mac_if.TxBitstuffEnableH = 1'b0;
  assign usb_20_mac_if.testbench_clock = phy_clk;

  // --------------------------------------------------------------------------
  // Testbench control and UVM startup
  // --------------------------------------------------------------------------
  initial begin
    usb_20_mac_if.utmi_dut_mac_if.generate_clk = 1'b1;
    `uvm_info("USB_TOP", "SVT PHY owns suspend-gated UTMI CLK; DUT wakeup is required", UVM_LOW)
  end

  // FUTUREFIX: Pass bus_reset_n and phy_clock_locked to UVM through a USB control VIF so tests can control reset and PHY lock sequencing.
  initial begin
    `uvm_info("USB_TOP", "Reset asserted; starting bus and UTMI PHY clocks", UVM_LOW)
    // Establish PHY lock before releasing the AXI reset.
    repeat (8) @(negedge bus_clk);
    phy_clock_locked = 1'b1;
    repeat (8) @(negedge bus_clk);
    bus_reset_n = 1'b1;
    `uvm_info("USB_TOP", "PHY clock lock established and reset released", UVM_LOW)
  end

  initial begin
    // The native Avery interfaces are macro-sized and must agree with the
    // parameterized AXI interfaces connected to the DUT.
    if (AAXI_DATA_WIDTH != USB_AXI_DATA_WIDTH ||
        AAXI_ADDR_WIDTH != USB_AXI_ADDR_WIDTH ||
        AAXI_ARUSER_WIDTH != USB_TB_AXI_USER_WIDTH ||
        AAXI_WUSER_WIDTH != USB_TB_AXI_USER_WIDTH ||
        AAXI_BUSER_WIDTH != USB_TB_AXI_USER_WIDTH ||
        AAXI_RUSER_WIDTH != USB_TB_AXI_USER_WIDTH) begin
      `uvm_fatal("USB_CONFIG", "Avery widths do not match the USB testbench configuration")
    end
`ifndef AVERY_ASSERT_ON
    `uvm_fatal("USB_CONFIG", "AVERY_ASSERT_ON is required for continuous AXI protocol checking")
`endif
    // Publish the four independent AXI managers and USB PHY to UVM.
    uvm_config_db#(virtual aaxi_intf)::set(null, "uvm_test_top.env", "combo_vif", combo_manager_vif);
    uvm_config_db#(virtual aaxi_intf)::set(null, "uvm_test_top.env", "dev0_memory_vif", dev0_memory_manager_vif);
    uvm_config_db#(virtual aaxi_intf)::set(null, "uvm_test_top.env", "dev1_csr_vif", dev1_csr_manager_vif);
    uvm_config_db#(virtual aaxi_intf)::set(null, "uvm_test_top.env", "dev1_memory_vif", dev1_memory_manager_vif);
    uvm_config_db#(virtual svt_usb_if)::set(null, "uvm_test_top.env", "usb_20_mac_if", usb_20_mac_if);
    run_test();
  end
endmodule
