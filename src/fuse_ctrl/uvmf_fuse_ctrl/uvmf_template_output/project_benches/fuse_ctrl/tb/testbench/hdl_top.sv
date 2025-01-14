//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
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

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------                     
//               
// Description: This top level module instantiates all synthesizable
//    static content.  This and tb_top.sv are the two top level modules
//    of the simulation.  
//
//    This module instantiates the following:
//        DUT: The Design Under Test
//        Interfaces:  Signal bundles that contain signals connected to DUT
//        Driver BFM's: BFM's that actively drive interface signals
//        Monitor BFM's: BFM's that passively monitor interface signals
//
//----------------------------------------------------------------------

//----------------------------------------------------------------------
//

module hdl_top;

import fuse_ctrl_parameters_pkg::*;
import uvmf_base_pkg_hdl::*;
import axi_pkg::*;

  // pragma attribute hdl_top partition_module_xrtl                                            
// pragma uvmf custom clock_generator begin
  bit clk;
  // Instantiate a clk driver 
  // tbx clkgen
  initial begin
    clk = 0;
    #0ns;
    forever begin
      clk = ~clk;
      #5ns;
    end
  end
// pragma uvmf custom clock_generator end

// pragma uvmf custom reset_generator begin
  bit rst;
  // Instantiate a rst driver
  // tbx clkgen
  initial begin
    rst = 0; 
    #200ns;
    rst =  1; 
  end
// pragma uvmf custom reset_generator end

  // pragma uvmf custom module_item_additional begin
  logic   edn_clk;
  logic   edn_rst_n;

  localparam MemInitFile = "/home/ws/caliptra/anjpar/ws1/chipsalliance/caliptra-rtl/src/fuse_ctrl/data/otp-img.2048.vmem";
  // pragma uvmf custom module_item_additional end

  // Instantiate the signal bundle, monitor bfm and driver bfm for each interface.
  // The signal bundle, _if, contains signals to be connected to the DUT.
  // The monitor, monitor_bfm, observes the bus, _if, and captures transactions.
  // The driver, driver_bfm, drives transactions onto the bus, _if.
  fuse_ctrl_rst_in_if  fuse_ctrl_rst_in_agent_bus(
     // pragma uvmf custom fuse_ctrl_rst_in_agent_bus_connections begin
     .clk_i(clk), .rst_ni(rst)
     // pragma uvmf custom fuse_ctrl_rst_in_agent_bus_connections end
     );
  fuse_ctrl_rst_out_if  fuse_ctrl_rst_out_agent_bus(
     // pragma uvmf custom fuse_ctrl_rst_out_agent_bus_connections begin
     .clk_i(clk), .rst_ni(rst)
     // pragma uvmf custom fuse_ctrl_rst_out_agent_bus_connections end
     );
  fuse_ctrl_core_axi_write_in_if  fuse_ctrl_core_axi_write_in_if_agent_bus(
     // pragma uvmf custom fuse_ctrl_core_axi_write_in_if_agent_bus_connections begin
     .clk_i(clk), .rst_ni(rst)
     // pragma uvmf custom fuse_ctrl_core_axi_write_in_if_agent_bus_connections end
     );
  fuse_ctrl_core_axi_write_out_if  fuse_ctrl_core_axi_write_out_if_agent_bus(
     // pragma uvmf custom fuse_ctrl_core_axi_write_out_if_agent_bus_connections begin
     .clk_i(clk), .rst_ni(rst)
     // pragma uvmf custom fuse_ctrl_core_axi_write_out_if_agent_bus_connections end
     );
  fuse_ctrl_prim_axi_write_in_if  fuse_ctrl_prim_axi_write_in_if_agent_bus(
     // pragma uvmf custom fuse_ctrl_prim_axi_write_in_if_agent_bus_connections begin
     .clk_i(clk), .rst_ni(rst)
     // pragma uvmf custom fuse_ctrl_prim_axi_write_in_if_agent_bus_connections end
     );
  fuse_ctrl_prim_axi_write_out_if  fuse_ctrl_prim_axi_write_out_if_agent_bus(
     // pragma uvmf custom fuse_ctrl_prim_axi_write_out_if_agent_bus_connections begin
     .clk_i(clk), .rst_ni(rst)
     // pragma uvmf custom fuse_ctrl_prim_axi_write_out_if_agent_bus_connections end
     );
  fuse_ctrl_core_axi_read_in_if  fuse_ctrl_core_axi_read_in_if_agent_bus(
     // pragma uvmf custom fuse_ctrl_core_axi_read_in_if_agent_bus_connections begin
     .clk_i(clk), .rst_ni(rst)
     // pragma uvmf custom fuse_ctrl_core_axi_read_in_if_agent_bus_connections end
     );
  fuse_ctrl_core_axi_read_out_if  fuse_ctrl_core_axi_read_out_if_agent_bus(
     // pragma uvmf custom fuse_ctrl_core_axi_read_out_if_agent_bus_connections begin
     .clk_i(clk), .rst_ni(rst)
     // pragma uvmf custom fuse_ctrl_core_axi_read_out_if_agent_bus_connections end
     );
  fuse_ctrl_prim_axi_read_in_if  fuse_ctrl_prim_axi_read_in_if_agent_bus(
     // pragma uvmf custom fuse_ctrl_prim_axi_read_in_if_agent_bus_connections begin
     .clk_i(clk), .rst_ni(rst)
     // pragma uvmf custom fuse_ctrl_prim_axi_read_in_if_agent_bus_connections end
     );
  fuse_ctrl_prim_axi_read_out_if  fuse_ctrl_prim_axi_read_out_if_agent_bus(
     // pragma uvmf custom fuse_ctrl_prim_axi_read_out_if_agent_bus_connections begin
     .clk_i(clk), .rst_ni(rst)
     // pragma uvmf custom fuse_ctrl_prim_axi_read_out_if_agent_bus_connections end
     );
  fuse_ctrl_secreg_axi_read_in_if  fuse_ctrl_secreg_axi_read_in_if_agent_bus(
     // pragma uvmf custom fuse_ctrl_secreg_axi_read_in_if_agent_bus_connections begin
     .clk_i(clk), .rst_ni(rst)
     // pragma uvmf custom fuse_ctrl_secreg_axi_read_in_if_agent_bus_connections end
     );
  fuse_ctrl_secreg_axi_read_out_if  fuse_ctrl_secreg_axi_read_out_if_agent_bus(
     // pragma uvmf custom fuse_ctrl_secreg_axi_read_out_if_agent_bus_connections begin
     .clk_i(clk), .rst_ni(rst)
     // pragma uvmf custom fuse_ctrl_secreg_axi_read_out_if_agent_bus_connections end
     );
  fuse_ctrl_lc_otp_in_if  fuse_ctrl_lc_otp_in_if_agent_bus(
     // pragma uvmf custom fuse_ctrl_lc_otp_in_if_agent_bus_connections begin
     .clk_i(clk), .rst_ni(rst)
     // pragma uvmf custom fuse_ctrl_lc_otp_in_if_agent_bus_connections end
     );
  fuse_ctrl_lc_otp_out_if  fuse_ctrl_lc_otp_out_if_agent_bus(
     // pragma uvmf custom fuse_ctrl_lc_otp_out_if_agent_bus_connections begin
     .clk_i(clk), .rst_ni(rst)
     // pragma uvmf custom fuse_ctrl_lc_otp_out_if_agent_bus_connections end
     );
  fuse_ctrl_in_if  fuse_ctrl_in_if_agent_bus(
     // pragma uvmf custom fuse_ctrl_in_if_agent_bus_connections begin
     .clk_i(clk), .rst_ni(rst)
     // pragma uvmf custom fuse_ctrl_in_if_agent_bus_connections end
     );
  fuse_ctrl_out_if  fuse_ctrl_out_if_agent_bus(
     // pragma uvmf custom fuse_ctrl_out_if_agent_bus_connections begin
     .clk_i(clk), .rst_ni(rst)
     // pragma uvmf custom fuse_ctrl_out_if_agent_bus_connections end
     );
  fuse_ctrl_rst_in_monitor_bfm  fuse_ctrl_rst_in_agent_mon_bfm(fuse_ctrl_rst_in_agent_bus.monitor_port);
  fuse_ctrl_rst_out_monitor_bfm  fuse_ctrl_rst_out_agent_mon_bfm(fuse_ctrl_rst_out_agent_bus.monitor_port);
  fuse_ctrl_core_axi_write_in_monitor_bfm  fuse_ctrl_core_axi_write_in_if_agent_mon_bfm(fuse_ctrl_core_axi_write_in_if_agent_bus.monitor_port);
  fuse_ctrl_core_axi_write_out_monitor_bfm  fuse_ctrl_core_axi_write_out_if_agent_mon_bfm(fuse_ctrl_core_axi_write_out_if_agent_bus.monitor_port);
  fuse_ctrl_prim_axi_write_in_monitor_bfm  fuse_ctrl_prim_axi_write_in_if_agent_mon_bfm(fuse_ctrl_prim_axi_write_in_if_agent_bus.monitor_port);
  fuse_ctrl_prim_axi_write_out_monitor_bfm  fuse_ctrl_prim_axi_write_out_if_agent_mon_bfm(fuse_ctrl_prim_axi_write_out_if_agent_bus.monitor_port);
  fuse_ctrl_core_axi_read_in_monitor_bfm  fuse_ctrl_core_axi_read_in_if_agent_mon_bfm(fuse_ctrl_core_axi_read_in_if_agent_bus.monitor_port);
  fuse_ctrl_core_axi_read_out_monitor_bfm  fuse_ctrl_core_axi_read_out_if_agent_mon_bfm(fuse_ctrl_core_axi_read_out_if_agent_bus.monitor_port);
  fuse_ctrl_prim_axi_read_in_monitor_bfm  fuse_ctrl_prim_axi_read_in_if_agent_mon_bfm(fuse_ctrl_prim_axi_read_in_if_agent_bus.monitor_port);
  fuse_ctrl_prim_axi_read_out_monitor_bfm  fuse_ctrl_prim_axi_read_out_if_agent_mon_bfm(fuse_ctrl_prim_axi_read_out_if_agent_bus.monitor_port);
  fuse_ctrl_secreg_axi_read_in_monitor_bfm  fuse_ctrl_secreg_axi_read_in_if_agent_mon_bfm(fuse_ctrl_secreg_axi_read_in_if_agent_bus.monitor_port);
  fuse_ctrl_secreg_axi_read_out_monitor_bfm  fuse_ctrl_secreg_axi_read_out_if_agent_mon_bfm(fuse_ctrl_secreg_axi_read_out_if_agent_bus.monitor_port);
  fuse_ctrl_lc_otp_in_monitor_bfm  fuse_ctrl_lc_otp_in_if_agent_mon_bfm(fuse_ctrl_lc_otp_in_if_agent_bus.monitor_port);
  fuse_ctrl_lc_otp_out_monitor_bfm  fuse_ctrl_lc_otp_out_if_agent_mon_bfm(fuse_ctrl_lc_otp_out_if_agent_bus.monitor_port);
  fuse_ctrl_in_monitor_bfm  fuse_ctrl_in_if_agent_mon_bfm(fuse_ctrl_in_if_agent_bus.monitor_port);
  fuse_ctrl_out_monitor_bfm  fuse_ctrl_out_if_agent_mon_bfm(fuse_ctrl_out_if_agent_bus.monitor_port);
  fuse_ctrl_rst_in_driver_bfm  fuse_ctrl_rst_in_agent_drv_bfm(fuse_ctrl_rst_in_agent_bus.initiator_port);
  fuse_ctrl_core_axi_write_in_driver_bfm  fuse_ctrl_core_axi_write_in_if_agent_drv_bfm(fuse_ctrl_core_axi_write_in_if_agent_bus.initiator_port);
  fuse_ctrl_prim_axi_write_in_driver_bfm  fuse_ctrl_prim_axi_write_in_if_agent_drv_bfm(fuse_ctrl_prim_axi_write_in_if_agent_bus.initiator_port);
  fuse_ctrl_core_axi_read_in_driver_bfm  fuse_ctrl_core_axi_read_in_if_agent_drv_bfm(fuse_ctrl_core_axi_read_in_if_agent_bus.initiator_port);
  fuse_ctrl_prim_axi_read_in_driver_bfm  fuse_ctrl_prim_axi_read_in_if_agent_drv_bfm(fuse_ctrl_prim_axi_read_in_if_agent_bus.initiator_port);
  fuse_ctrl_secreg_axi_read_in_driver_bfm  fuse_ctrl_secreg_axi_read_in_if_agent_drv_bfm(fuse_ctrl_secreg_axi_read_in_if_agent_bus.initiator_port);
  fuse_ctrl_lc_otp_in_driver_bfm  fuse_ctrl_lc_otp_in_if_agent_drv_bfm(fuse_ctrl_lc_otp_in_if_agent_bus.initiator_port);
  fuse_ctrl_in_driver_bfm  fuse_ctrl_in_if_agent_drv_bfm(fuse_ctrl_in_if_agent_bus.initiator_port);

  // pragma uvmf custom dut_instantiation begin
  // UVMF_CHANGE_ME : Add DUT and connect to signals in _bus interfaces listed above
  // Instantiate your DUT here
  // These DUT's instantiated to show verilog and vhdl instantiation
  //verilog_dut         dut_verilog(   .clk(clk), .rst(rst), .in_signal(vhdl_to_verilog_signal), .out_signal(verilog_to_vhdl_signal));
  //vhdl_dut            dut_vhdl   (   .clk(clk), .rst(rst), .in_signal(verilog_to_vhdl_signal), .out_signal(vhdl_to_verilog_signal));

  otp_ctrl_top #(
    .MemInitFile        (MemInitFile) 
  ) dut (
    .clk_i                      (fuse_ctrl_rst_in_agent_bus.clk_i     ),
    .rst_ni                     (fuse_ctrl_rst_in_agent_bus.rst_ni ),
    // edn
    .clk_edn_i                  (edn_clk    ),
    .rst_edn_ni                 (edn_rst_n  ),
    .edn_o                      (fuse_ctrl_out_if_agent_bus.edn_o), //(edn_if[0].req ),
    .edn_i                      (fuse_ctrl_in_if_agent_bus.edn_i), //({edn_if[0].ack, edn_if[0].d_data}),
    // AXI interface
    .s_core_axi_r_if            (axi_core_if.r_sub),
    .s_core_axi_w_if            (axi_core_if.w_sub),
    .s_prim_axi_r_if            (axi_prim_if.r_sub),
    .s_prim_axi_w_if            (axi_prim_if.w_sub),
    .s_secreg_axi_r_if          (axi_secreg_if.r_sub),
    // interrupt
    .intr_otp_operation_done_o  (fuse_ctrl_out_if_agent_bus.intr_otp_operation_done_o),
    .intr_otp_error_o           (fuse_ctrl_out_if_agent_bus.intr_otp_error_o),
    // alert
    .alert_rx_i                 (fuse_ctrl_in_if_agent_bus.alert_rx_i  ), //(alert_rx      parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ALERT_TEST_OFFSET = 13'h c;
    .alert_tx_o                 (fuse_ctrl_out_if_agent_bus.alert_tx_o ), //(alert_tx   ),
    // ast
    .obs_ctrl_i                 (fuse_ctrl_in_if_agent_bus.obs_ctrl_i), //(otp_ctrl_if.obs_ctrl_i),
    .otp_obs_o                  (fuse_ctrl_out_if_agent_bus.otp_obs_o), 
    .otp_ast_pwr_seq_o          (fuse_ctrl_out_if_agent_bus.otp_ast_pwr_seq_o), //(ast_req),
    .otp_ast_pwr_seq_h_i        (fuse_ctrl_in_if_agent_bus.otp_ast_pwr_seq_h_i), //(otp_ctrl_if.otp_ast_pwr_seq_h_i),
    // pwrmgr
    .pwr_otp_i                  (fuse_ctrl_rst_in_agent_bus.pwr_otp_i), //(otp_ctrl_if.pwr_otp_init_i),
    .pwr_otp_o                  (fuse_ctrl_rst_out_agent_bus.pwr_otp_o), //({otp_ctrl_if.pwr_otp_done_o, otp_ctrl_if.pwr_otp_idle_o}),
    // lc
    .lc_otp_vendor_test_i       (fuse_ctrl_lc_otp_in_if_agent_bus.lc_otp_vendor_test_i), //(otp_ctrl_if.otp_vendor_test_ctrl_i),
    .lc_otp_vendor_test_o		(fuse_ctrl_lc_otp_out_if_agent_bus.lc_otp_vendor_test_o), //(otp_ctrl_if.otp_vendor_test_status_o),
    .lc_otp_program_i		    (fuse_ctrl_lc_otp_in_if_agent_bus.lc_otp_program_i), //({lc_prog_if.req, lc_prog_if.h_data}),
    .lc_otp_program_o		    (fuse_ctrl_lc_otp_out_if_agent_bus.lc_otp_program_o), //({lc_prog_if.d_data, lc_prog_if.ack}),
    //.lc_creator_seed_sw_rw_en_i	(lc_creator_seed_sw_rw_en_i), //(otp_ctrl_if.lc_creator_seed_sw_rw_en_i),
    //.lc_owner_seed_sw_rw_en_i	(lc_owner_seed_sw_rw_en_i), //(otp_ctrl_if.lc_owner_seed_sw_rw_en_i),
    //.lc_seed_hw_rd_en_i		    (lc_seed_hw_rd_en_i), //(otp_ctrl_if.lc_seed_hw_rd_en_i),
    .lc_dft_en_i		        (fuse_ctrl_lc_otp_in_if_agent_bus.lc_dft_en_i), //(otp_ctrl_if.lc_dft_en_i),
    .lc_escalate_en_i		    (fuse_ctrl_lc_otp_in_if_agent_bus.lc_escalate_en_i), //(otp_ctrl_if.lc_escalate_en_i),
    .lc_check_byp_en_i		    (fuse_ctrl_lc_otp_in_if_agent_bus.lc_check_byp_en_i), //(otp_ctrl_if.lc_check_byp_en_i),
    .otp_lc_data_o		        (fuse_ctrl_lc_otp_out_if_agent_bus.otp_lc_data_o), //(otp_ctrl_if.lc_data_o),
        

    .otp_broadcast_o            (fuse_ctrl_out_if_agent_bus.otp_broadcast_o), //(otp_ctrl_if.otp_broadcast_o),
    .otp_ext_voltage_h_io       (fuse_ctrl_rst_in_agent_bus.otp_ext_voltage_h_io),
    //scan
    .scan_en_i                  (fuse_ctrl_in_if_agent_bus.scan_en_i), //(otp_ctrl_if.scan_en_i),
    .scan_rst_ni                (fuse_ctrl_in_if_agent_bus.scan_rst_ni), //(otp_ctrl_if.scan_rst_ni),
    .scanmode_i                 (fuse_ctrl_in_if_agent_bus.scanmode_i), //(otp_ctrl_if.scanmode_i),

    // Test-related GPIO output
    .cio_test_o                 (fuse_ctrl_out_if_agent_bus.cio_test_o), //(otp_ctrl_if.cio_test_o),
    .cio_test_en_o              (fuse_ctrl_out_if_agent_bus.cio_test_en_o) //(otp_ctrl_if.cio_test_en_o)
  );

  // AXI Core Interface
  axi_if #(
   .AW (AXI_AW),
   .DW (AXI_DW),
   .IW (AXI_IW),
   .UW (AXI_UW)
   ) axi_core_if (
      .clk    (fuse_ctrl_rst_in_agent_bus.clk_i ),
      .rst_n  (fuse_ctrl_rst_in_agent_bus.rst_ni )
   );

   // AXI Prim Interface
   axi_if #(
      .AW (AXI_AW),
      .DW (AXI_DW),
      .IW (AXI_IW),
      .UW (AXI_UW)
   ) axi_prim_if (
      .clk    (fuse_ctrl_rst_in_agent_bus.clk_i ),
      .rst_n  (fuse_ctrl_rst_in_agent_bus.rst_ni)
   );

   // AXI Secret Reg Interface
   axi_if #(
      .AW (AXI_AW),
      .DW (AXI_DW),
      .IW (AXI_IW),
      .UW (AXI_UW)
   ) axi_secreg_if (
      .clk    (fuse_ctrl_rst_in_agent_bus.clk_i ),
      .rst_n  (fuse_ctrl_rst_in_agent_bus.rst_ni)
   );

   // Core AXI IF
   assign fuse_ctrl_core_axi_write_in_if_agent_bus.awaddr     = axi_core_if.awaddr;
   assign fuse_ctrl_core_axi_write_in_if_agent_bus.awburst    = axi_core_if.awburst;
   assign fuse_ctrl_core_axi_write_in_if_agent_bus.awsize     = axi_core_if.awsize;
   assign fuse_ctrl_core_axi_write_in_if_agent_bus.awlen      = axi_core_if.awlen;
   assign fuse_ctrl_core_axi_write_in_if_agent_bus.awuser     = axi_core_if.awuser;
   assign fuse_ctrl_core_axi_write_in_if_agent_bus.awid       = axi_core_if.awid;
   assign fuse_ctrl_core_axi_write_in_if_agent_bus.awlock     = axi_core_if.awlock;
   assign fuse_ctrl_core_axi_write_in_if_agent_bus.awvalid    = axi_core_if.awvalid;
   assign fuse_ctrl_core_axi_write_in_if_agent_bus.wdata      = axi_core_if.wdata;
   assign fuse_ctrl_core_axi_write_in_if_agent_bus.wstrb      = axi_core_if.wstrb;
   assign fuse_ctrl_core_axi_write_in_if_agent_bus.wlast      = axi_core_if.wlast;
   assign fuse_ctrl_core_axi_write_in_if_agent_bus.wvalid     = axi_core_if.wvalid;
   assign fuse_ctrl_core_axi_write_in_if_agent_bus.bready     = axi_core_if.bready;
   
   assign fuse_ctrl_core_axi_write_out_if_agent_bus.awready    = axi_core_if.awready;
   assign fuse_ctrl_core_axi_write_out_if_agent_bus.wready     = axi_core_if.wready;
   assign fuse_ctrl_core_axi_write_out_if_agent_bus.bresp      = axi_core_if.bresp;
   assign fuse_ctrl_core_axi_write_out_if_agent_bus.bvalid     = axi_core_if.bvalid;
   assign fuse_ctrl_core_axi_write_out_if_agent_bus.bid        = axi_core_if.bid;

   assign fuse_ctrl_core_axi_read_in_if_agent_bus.araddr     = axi_core_if.araddr;
   assign fuse_ctrl_core_axi_read_in_if_agent_bus.arburst    = axi_core_if.arburst;
   assign fuse_ctrl_core_axi_read_in_if_agent_bus.arsize     = axi_core_if.arsize;
   assign fuse_ctrl_core_axi_read_in_if_agent_bus.arlen      = axi_core_if.arlen;
   assign fuse_ctrl_core_axi_read_in_if_agent_bus.aruser     = axi_core_if.aruser;
   assign fuse_ctrl_core_axi_read_in_if_agent_bus.arid       = axi_core_if.arid;
   assign fuse_ctrl_core_axi_read_in_if_agent_bus.arlock     = axi_core_if.arlock;
   assign fuse_ctrl_core_axi_read_in_if_agent_bus.arvalid    = axi_core_if.arvalid;
   assign fuse_ctrl_core_axi_read_in_if_agent_bus.rready     = axi_core_if.rready;
   
   assign fuse_ctrl_core_axi_read_out_if_agent_bus.arready    = axi_core_if.arready;
   assign fuse_ctrl_core_axi_read_out_if_agent_bus.rdata      = axi_core_if.rdata;
   assign fuse_ctrl_core_axi_read_out_if_agent_bus.rresp      = axi_core_if.rresp;
   assign fuse_ctrl_core_axi_read_out_if_agent_bus.rid        = axi_core_if.rid;
   assign fuse_ctrl_core_axi_read_out_if_agent_bus.rvalid     = axi_core_if.rvalid;
   assign fuse_ctrl_core_axi_read_out_if_agent_bus.rlast      = axi_core_if.rlast;

   // Prim AXI IF
   assign fuse_ctrl_prim_axi_write_in_if_agent_bus.awaddr     = axi_prim_if.awaddr;
   assign fuse_ctrl_prim_axi_write_in_if_agent_bus.awburst    = axi_prim_if.awburst;
   assign fuse_ctrl_prim_axi_write_in_if_agent_bus.awsize     = axi_prim_if.awsize;
   assign fuse_ctrl_prim_axi_write_in_if_agent_bus.awlen      = axi_prim_if.awlen;
   assign fuse_ctrl_prim_axi_write_in_if_agent_bus.awuser     = axi_prim_if.awuser;
   assign fuse_ctrl_prim_axi_write_in_if_agent_bus.awid       = axi_prim_if.awid;
   assign fuse_ctrl_prim_axi_write_in_if_agent_bus.awlock     = axi_prim_if.awlock;
   assign fuse_ctrl_prim_axi_write_in_if_agent_bus.awvalid    = axi_prim_if.awvalid;
   assign fuse_ctrl_prim_axi_write_in_if_agent_bus.wdata      = axi_prim_if.wdata;
   assign fuse_ctrl_prim_axi_write_in_if_agent_bus.wstrb      = axi_prim_if.wstrb;
   assign fuse_ctrl_prim_axi_write_in_if_agent_bus.wlast      = axi_prim_if.wlast;
   assign fuse_ctrl_prim_axi_write_in_if_agent_bus.wvalid     = axi_prim_if.wvalid;
   assign fuse_ctrl_prim_axi_write_in_if_agent_bus.bready     = axi_prim_if.bready;
   assign fuse_ctrl_prim_axi_write_out_if_agent_bus.awready    = axi_prim_if.awready;
   assign fuse_ctrl_prim_axi_write_out_if_agent_bus.wready     = axi_prim_if.wready;
   assign fuse_ctrl_prim_axi_write_out_if_agent_bus.bresp      = axi_prim_if.bresp;
   assign fuse_ctrl_prim_axi_write_out_if_agent_bus.bvalid     = axi_prim_if.bvalid;
   assign fuse_ctrl_prim_axi_write_out_if_agent_bus.bid        = axi_prim_if.bid;

   assign fuse_ctrl_prim_axi_read_in_if_agent_bus.araddr     = axi_prim_if.araddr;
   assign fuse_ctrl_prim_axi_read_in_if_agent_bus.arburst    = axi_prim_if.arburst;
   assign fuse_ctrl_prim_axi_read_in_if_agent_bus.arsize     = axi_prim_if.arsize;
   assign fuse_ctrl_prim_axi_read_in_if_agent_bus.arlen      = axi_prim_if.arlen;
   assign fuse_ctrl_prim_axi_read_in_if_agent_bus.aruser     = axi_prim_if.aruser;
   assign fuse_ctrl_prim_axi_read_in_if_agent_bus.arid       = axi_prim_if.arid;
   assign fuse_ctrl_prim_axi_read_in_if_agent_bus.arlock     = axi_prim_if.arlock;
   assign fuse_ctrl_prim_axi_read_in_if_agent_bus.arvalid    = axi_prim_if.arvalid;
   assign fuse_ctrl_prim_axi_read_in_if_agent_bus.rready     = axi_prim_if.rready;
   
   assign fuse_ctrl_prim_axi_read_out_if_agent_bus.arready    = axi_prim_if.arready;
   assign fuse_ctrl_prim_axi_read_out_if_agent_bus.rdata      = axi_prim_if.rdata;
   assign fuse_ctrl_prim_axi_read_out_if_agent_bus.rresp      = axi_prim_if.rresp;
   assign fuse_ctrl_prim_axi_read_out_if_agent_bus.rid        = axi_prim_if.rid;
   assign fuse_ctrl_prim_axi_read_out_if_agent_bus.rvalid     = axi_prim_if.rvalid;
   assign fuse_ctrl_prim_axi_read_out_if_agent_bus.rlast      = axi_prim_if.rlast;

   // Secreg AXI IF
   assign fuse_ctrl_secreg_axi_read_in_if_agent_bus.araddr     = axi_secreg_if.araddr;
   assign fuse_ctrl_secreg_axi_read_in_if_agent_bus.arburst    = axi_secreg_if.arburst;
   assign fuse_ctrl_secreg_axi_read_in_if_agent_bus.arsize     = axi_secreg_if.arsize;
   assign fuse_ctrl_secreg_axi_read_in_if_agent_bus.arlen      = axi_secreg_if.arlen;
   assign fuse_ctrl_secreg_axi_read_in_if_agent_bus.aruser     = axi_secreg_if.aruser;
   assign fuse_ctrl_secreg_axi_read_in_if_agent_bus.arid       = axi_secreg_if.arid;
   assign fuse_ctrl_secreg_axi_read_in_if_agent_bus.arlock     = axi_secreg_if.arlock;
   assign fuse_ctrl_secreg_axi_read_in_if_agent_bus.arvalid    = axi_secreg_if.arvalid;
   assign fuse_ctrl_secreg_axi_read_in_if_agent_bus.rready     = axi_secreg_if.rready;
   
   assign fuse_ctrl_secreg_axi_read_out_if_agent_bus.arready    = axi_secreg_if.arready;
   assign fuse_ctrl_secreg_axi_read_out_if_agent_bus.rdata      = axi_secreg_if.rdata;
   assign fuse_ctrl_secreg_axi_read_out_if_agent_bus.rresp      = axi_secreg_if.rresp;
   assign fuse_ctrl_secreg_axi_read_out_if_agent_bus.rid        = axi_secreg_if.rid;
   assign fuse_ctrl_secreg_axi_read_out_if_agent_bus.rvalid     = axi_secreg_if.rvalid;
   assign fuse_ctrl_secreg_axi_read_out_if_agent_bus.rlast      = axi_secreg_if.rlast;
  // pragma uvmf custom dut_instantiation end

  initial begin      // tbx vif_binding_block 
    import uvm_pkg::uvm_config_db;
    // The monitor_bfm and driver_bfm for each interface is placed into the uvm_config_db.
    // They are placed into the uvm_config_db using the string names defined in the parameters package.
    // The string names are passed to the agent configurations by test_top through the top level configuration.
    // They are retrieved by the agents configuration class for use by the agent.
    uvm_config_db #( virtual fuse_ctrl_rst_in_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_rst_in_agent_BFM , fuse_ctrl_rst_in_agent_mon_bfm ); 
    uvm_config_db #( virtual fuse_ctrl_rst_out_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_rst_out_agent_BFM , fuse_ctrl_rst_out_agent_mon_bfm ); 
    uvm_config_db #( virtual fuse_ctrl_core_axi_write_in_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_core_axi_write_in_if_agent_BFM , fuse_ctrl_core_axi_write_in_if_agent_mon_bfm ); 
    uvm_config_db #( virtual fuse_ctrl_core_axi_write_out_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_core_axi_write_out_if_agent_BFM , fuse_ctrl_core_axi_write_out_if_agent_mon_bfm ); 
    uvm_config_db #( virtual fuse_ctrl_prim_axi_write_in_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_prim_axi_write_in_if_agent_BFM , fuse_ctrl_prim_axi_write_in_if_agent_mon_bfm ); 
    uvm_config_db #( virtual fuse_ctrl_prim_axi_write_out_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_prim_axi_write_out_if_agent_BFM , fuse_ctrl_prim_axi_write_out_if_agent_mon_bfm ); 
    uvm_config_db #( virtual fuse_ctrl_core_axi_read_in_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_core_axi_read_in_if_agent_BFM , fuse_ctrl_core_axi_read_in_if_agent_mon_bfm ); 
    uvm_config_db #( virtual fuse_ctrl_core_axi_read_out_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_core_axi_read_out_if_agent_BFM , fuse_ctrl_core_axi_read_out_if_agent_mon_bfm ); 
    uvm_config_db #( virtual fuse_ctrl_prim_axi_read_in_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_prim_axi_read_in_if_agent_BFM , fuse_ctrl_prim_axi_read_in_if_agent_mon_bfm ); 
    uvm_config_db #( virtual fuse_ctrl_prim_axi_read_out_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_prim_axi_read_out_if_agent_BFM , fuse_ctrl_prim_axi_read_out_if_agent_mon_bfm ); 
    uvm_config_db #( virtual fuse_ctrl_secreg_axi_read_in_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_secreg_axi_read_in_if_agent_BFM , fuse_ctrl_secreg_axi_read_in_if_agent_mon_bfm ); 
    uvm_config_db #( virtual fuse_ctrl_secreg_axi_read_out_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_secreg_axi_read_out_if_agent_BFM , fuse_ctrl_secreg_axi_read_out_if_agent_mon_bfm ); 
    uvm_config_db #( virtual fuse_ctrl_lc_otp_in_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_lc_otp_in_if_agent_BFM , fuse_ctrl_lc_otp_in_if_agent_mon_bfm ); 
    uvm_config_db #( virtual fuse_ctrl_lc_otp_out_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_lc_otp_out_if_agent_BFM , fuse_ctrl_lc_otp_out_if_agent_mon_bfm ); 
    uvm_config_db #( virtual fuse_ctrl_in_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_in_if_agent_BFM , fuse_ctrl_in_if_agent_mon_bfm ); 
    uvm_config_db #( virtual fuse_ctrl_out_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_out_if_agent_BFM , fuse_ctrl_out_if_agent_mon_bfm ); 
    uvm_config_db #( virtual fuse_ctrl_rst_in_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_rst_in_agent_BFM , fuse_ctrl_rst_in_agent_drv_bfm  );
    uvm_config_db #( virtual fuse_ctrl_core_axi_write_in_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_core_axi_write_in_if_agent_BFM , fuse_ctrl_core_axi_write_in_if_agent_drv_bfm  );
    uvm_config_db #( virtual fuse_ctrl_prim_axi_write_in_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_prim_axi_write_in_if_agent_BFM , fuse_ctrl_prim_axi_write_in_if_agent_drv_bfm  );
    uvm_config_db #( virtual fuse_ctrl_core_axi_read_in_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_core_axi_read_in_if_agent_BFM , fuse_ctrl_core_axi_read_in_if_agent_drv_bfm  );
    uvm_config_db #( virtual fuse_ctrl_prim_axi_read_in_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_prim_axi_read_in_if_agent_BFM , fuse_ctrl_prim_axi_read_in_if_agent_drv_bfm  );
    uvm_config_db #( virtual fuse_ctrl_secreg_axi_read_in_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_secreg_axi_read_in_if_agent_BFM , fuse_ctrl_secreg_axi_read_in_if_agent_drv_bfm  );
    uvm_config_db #( virtual fuse_ctrl_lc_otp_in_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_lc_otp_in_if_agent_BFM , fuse_ctrl_lc_otp_in_if_agent_drv_bfm  );
    uvm_config_db #( virtual fuse_ctrl_in_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , fuse_ctrl_in_if_agent_BFM , fuse_ctrl_in_if_agent_drv_bfm  );
  end

endmodule

// pragma uvmf custom external begin
// pragma uvmf custom external end

