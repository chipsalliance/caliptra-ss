// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import spi_host_env_pkg::*;
  import spi_host_test_pkg::*;
  import caliptra_ss_spi_host_reg_pkg::*;

  import caliptra_ss_spi_device_pkg::caliptra_ss_passthrough_req_t;
  import caliptra_ss_spi_device_pkg::caliptra_ss_passthrough_rsp_t;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  localparam int unsigned AXI_AW = 32;
  localparam int unsigned AXI_DW = 32;
  localparam int unsigned AXI_UW = 32;
  localparam int unsigned AXI_IW = 1;

  wire clk, rst_n;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  logic                         cio_sck_o;
  logic                         cio_sck_en_o;
  logic [SPI_HOST_NUM_CS-1:0]   cio_csb_o;
  logic [SPI_HOST_NUM_CS-1:0]   cio_csb_en_o;
  logic [3:0]                   cio_sd_o;
  logic [3:0]                   cio_sd_en_o;
  logic [3:0]                   cio_sd_i;
  logic                         intr_error;
  logic                         intr_event;
  wire                          intg_error;

  caliptra_ss_passthrough_req_t passthrough_i;
  caliptra_ss_passthrough_rsp_t passthrough_o;

  // interfaces
  clk_rst_if   clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(.pins(interrupts));
  pins_if #(1) intg_error_if(.pins(intg_error));

  // Production Caliptra AXI4 interface connected to spi_host_axi
  axi_if #(
    .AW(AXI_AW),
    .DW(AXI_DW),
    .IW(AXI_IW),
    .UW(AXI_UW)
  ) axi_bus_if (
    .clk  (clk),
    .rst_n(rst_n)
  );

  // AXI Sub-interfaces for UVM AXI Manager Agent
  axi_write_request_if  aw_if (.clk_i(clk), .rst_ni(rst_n));
  axi_write_data_if     w_if  (.clk_i(clk), .rst_ni(rst_n));
  axi_write_response_if b_if  (.clk_i(clk), .rst_ni(rst_n));
  axi_read_request_if   ar_if (.clk_i(clk), .rst_ni(rst_n));
  axi_read_data_if      r_if  (.clk_i(clk), .rst_ni(rst_n));

  // Prevent compiler from optimizing away the test package (needed for UVM factory)
  spi_host_base_test dummy_test;

  // Connect AXI AW channel
  assign axi_bus_if.awvalid  = aw_if.awvalid;
  assign aw_if.awready       = axi_bus_if.awready;
  assign axi_bus_if.awaddr   = aw_if.awaddr[AXI_AW-1:0];
  assign axi_bus_if.awid     = aw_if.awid[AXI_IW-1:0];
  assign axi_bus_if.awlen    = aw_if.awlen;
  assign axi_bus_if.awsize   = aw_if.awsize;
  assign axi_bus_if.awburst  = aw_if.awburst;
  assign axi_bus_if.awlock   = aw_if.awlock;
  assign axi_bus_if.awcache  = aw_if.awcache;
  assign axi_bus_if.awprot   = aw_if.awprot;
  assign axi_bus_if.awqos    = aw_if.awqos;
  assign axi_bus_if.awregion = aw_if.awregion;
  assign axi_bus_if.awuser   = aw_if.awuser[AXI_UW-1:0];

  // Connect AXI W channel
  assign axi_bus_if.wvalid   = w_if.wvalid;
  assign w_if.wready         = axi_bus_if.wready;
  assign axi_bus_if.wdata    = w_if.wdata[AXI_DW-1:0];
  assign axi_bus_if.wstrb    = w_if.wstrb[(AXI_DW/8)-1:0];
  assign axi_bus_if.wlast    = w_if.wlast;
  assign axi_bus_if.wuser    = w_if.wuser[AXI_UW-1:0];

  // Connect AXI B channel
  assign b_if.bvalid         = axi_bus_if.bvalid;
  assign axi_bus_if.bready   = b_if.bready;
  assign b_if.bid            = {{(32-AXI_IW){1'b0}}, axi_bus_if.bid};
  assign b_if.bresp          = {1'b0, axi_bus_if.bresp};
  assign b_if.buser          = axi_bus_if.buser[15:0];

  // Connect AXI AR channel
  assign axi_bus_if.arvalid  = ar_if.arvalid;
  assign ar_if.arready       = axi_bus_if.arready;
  assign axi_bus_if.araddr   = ar_if.araddr[AXI_AW-1:0];
  assign axi_bus_if.arid     = ar_if.arid[AXI_IW-1:0];
  assign axi_bus_if.arlen    = ar_if.arlen;
  assign axi_bus_if.arsize   = ar_if.arsize;
  assign axi_bus_if.arburst  = ar_if.arburst;
  assign axi_bus_if.arlock   = ar_if.arlock;
  assign axi_bus_if.arcache  = ar_if.arcache;
  assign axi_bus_if.arprot   = ar_if.arprot;
  assign axi_bus_if.arqos    = ar_if.arqos;
  assign axi_bus_if.arregion = ar_if.arregion;
  assign axi_bus_if.aruser   = ar_if.aruser[AXI_UW-1:0];

  // Connect AXI R channel
  assign r_if.rvalid         = axi_bus_if.rvalid;
  assign axi_bus_if.rready   = r_if.rready;
  assign r_if.rid            = {{(32-AXI_IW){1'b0}}, axi_bus_if.rid};
  assign r_if.rdata          = {{(1024-AXI_DW){1'b0}}, axi_bus_if.rdata};
  assign r_if.rresp          = {1'b0, axi_bus_if.rresp};
  assign r_if.rlast          = axi_bus_if.rlast;
  assign r_if.ruser          = {{(528-AXI_UW){1'b0}}, axi_bus_if.ruser};

  wire [3:0] sd;
  pullup (sd[0]);
  pullup (sd[1]);
  pullup (sd[2]);
  pullup (sd[3]);

  spi_if             spi_if(.rst_n(rst_n), .sio(sd));
  spi_passthrough_if spi_passthrough_if(.rst_n(rst_n));

  // DUT: Production Caliptra-SS SPI Host AXI Subsystem Wrapper (axi2tlul + caliptra_ss_spi_host)
  spi_host_axi #(
    .NumCS   (SPI_HOST_NUM_CS),
    .CmdDepth(8),
    .AxiAw   (AXI_AW),
    .AxiDw   (AXI_DW),
    .AxiUw   (AXI_UW),
    .AxiIw   (AXI_IW)
  ) dut (
    .clk_i            (clk),
    .rst_ni           (rst_n),
    .s_axi_w_if       (axi_bus_if.w_sub),
    .s_axi_r_if       (axi_bus_if.r_sub),
    .intg_error_o     (intg_error),
    .cio_sck_o        (cio_sck_o),
    .cio_sck_en_o     (cio_sck_en_o),
    .cio_csb_o        (cio_csb_o),
    .cio_csb_en_o     (cio_csb_en_o),
    .cio_sd_o         (cio_sd_o),
    .cio_sd_en_o      (cio_sd_en_o),
    .cio_sd_i         (cio_sd_i),
    .passthrough_i    (passthrough_i),
    .passthrough_o    (passthrough_o),
    .intr_error_o     (intr_error),
    .intr_spi_event_o (intr_event)
  );

  // Contention-free single-bit TL-UL cmd_intg & data_intg SECDED fault injection on internal link
  always @(spi_passthrough_if.inject_cmd_intg_err or dut.u_axi2tlul_spi_host.i_sub2tlul.cmd_intg) begin
    if (spi_passthrough_if.inject_cmd_intg_err) begin
      force dut.tl_h2d.a_user.cmd_intg = dut.u_axi2tlul_spi_host.i_sub2tlul.cmd_intg ^ 7'h01;
    end else begin
      release dut.tl_h2d.a_user.cmd_intg;
    end
  end

  always @(spi_passthrough_if.inject_data_intg_err or dut.u_axi2tlul_spi_host.i_sub2tlul.data_intg) begin
    if (spi_passthrough_if.inject_data_intg_err) begin
      force dut.tl_h2d.a_user.data_intg = dut.u_axi2tlul_spi_host.i_sub2tlul.data_intg ^ 7'h01;
    end else begin
      release dut.tl_h2d.a_user.data_intg;
    end
  end

  assign passthrough_i.passthrough_en = spi_passthrough_if.passthrough_en;
  assign passthrough_i.sck_en         = spi_passthrough_if.sck_en;
  assign passthrough_i.csb_en         = spi_passthrough_if.csb_en;
  assign passthrough_i.s_en           = spi_passthrough_if.s_en;
  assign passthrough_i.csb            = spi_passthrough_if.csb;
  assign passthrough_i.sck            = spi_passthrough_if.sck;

  assign passthrough_i.s                 = spi_passthrough_if.is;
  assign spi_passthrough_if.os           = passthrough_o.s;
  assign spi_passthrough_if.cio_sck_o    = cio_sck_o;
  assign spi_passthrough_if.cio_sck_en_o = cio_sck_en_o;
  assign spi_passthrough_if.cio_csb_o    = 2'(cio_csb_o);
  assign spi_passthrough_if.cio_csb_en_o = 2'(cio_csb_en_o);
  assign spi_passthrough_if.cio_sd_en_o  = cio_sd_en_o;
  assign spi_passthrough_if.cio_sd_o     = cio_sd_o;

  assign cio_sd_i = spi_passthrough_if.passthrough_en ? spi_passthrough_if.cio_sd_i : sd;

  // configure spi_if i/o
  assign spi_if.sck = (cio_sck_en_o) ? cio_sck_o : 1'bz;
  for (genvar i = 0; i < 4; i++) begin : gen_tri_state
    assign sd[i]  = (cio_sd_en_o[i]) ? cio_sd_o[i] : 1'bz;

    if (i < 2) begin : gen_drive_csb
      if (i < SPI_HOST_NUM_CS) begin
        assign spi_if.csb[i] = cio_csb_en_o[i] ? cio_csb_o[i] : 1'b1;
      end else begin
        assign spi_if.csb[i] = 1'b1;
      end
    end
  end

  // Instantiate SPI Flash Models (gated by DUT pad enables and spi_if.en_flash_model)
  for (genvar i = 0; i < SPI_HOST_NUM_CS; i++) begin : gen_spi_flash
    spiflash #(
      .FlashSize (1024 * 1024), // 1MB
      .PageSize  (256),         // 256 Bytes
      .EnFastSim (1'b1)         // Fast simulation delays
    ) u_spi_flash (
      .sck ((spi_if.en_flash_model && cio_sck_en_o) ? cio_sck_o : 1'b0),
      .csb (spi_if.en_flash_model ? spi_if.csb[i] : 1'b1),
      .sd  (sd)
    );
  end

  assign interrupts[SpiHostError] = intr_error;
  assign interrupts[SpiHostEvent] = intr_event;

  // Bind
  bind dut.u_caliptra_ss_spi_host.u_spi_core spi_host_fsm_if fast_prescaler_bound_if();
  spi_host_cov_bind u_spi_host_cov_bind();
  spi_host_bind     u_spi_host_bind();

  // Single-sourced scoped assertion parameter waiver: Caliptra-SS spi_host outputs single-wire
  // intg_error_o rather than connecting an OpenTitan differential alert sender inside u_reg.
  defparam dut.u_caliptra_ss_spi_host.u_reg.u_prim_reg_we_check.u_caliptra_prim_onehot_check.EnableAlertTriggerSVA = 0;

  initial begin
`ifdef FSDB
    if ($test$plusargs("dump_waves") || $test$plusargs("waves")) begin
      $fsdbDumpfile("waves.fsdb");
      $fsdbDumpvars(0, tb, "+all");
      $fsdbDumpSVA(0, tb);
    end
`endif

    // Configure AXI sub-interface modes and widths matching spi_host_axi
    aw_if.if_mode = dv_utils_pkg::Host;
    w_if.if_mode  = dv_utils_pkg::Host;
    b_if.if_mode  = dv_utils_pkg::Host;
    ar_if.if_mode = dv_utils_pkg::Host;
    r_if.if_mode  = dv_utils_pkg::Host;

    aw_if.set_id_w_width(AXI_IW);
    aw_if.set_addr_width(AXI_AW);
    aw_if.set_user_req_width(AXI_UW);

    w_if.set_user_data_width(0);
    w_if.set_data_width(AXI_DW);

    b_if.set_id_w_width(AXI_IW);
    b_if.set_bresp_width(2);
    b_if.set_user_resp_width(16);

    ar_if.set_id_r_width(AXI_IW);
    ar_if.set_addr_width(AXI_AW);
    ar_if.set_user_req_width(AXI_UW);

    r_if.set_id_r_width(AXI_IW);
    r_if.set_user_data_width(0);
    r_if.set_data_width(AXI_DW);
    r_if.set_rresp_width(2);
    r_if.set_user_resp_width(16);

    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual pins_if #(1))::set(null, "*.env", "intg_error_vif", intg_error_if);
    uvm_config_db#(virtual spi_passthrough_if)::set(null, "*.env", "spi_passthrough_vif",
                                                 spi_passthrough_if);
    uvm_config_db#(virtual axi_write_request_if)::set(null, "*.env*", "aw_vif", aw_if);
    uvm_config_db#(virtual axi_write_data_if)::set(null, "*.env*", "w_vif", w_if);
    uvm_config_db#(virtual axi_write_response_if)::set(null, "*.env*", "b_vif", b_if);
    uvm_config_db#(virtual axi_read_request_if)::set(null, "*.env*", "ar_vif", ar_if);
    uvm_config_db#(virtual axi_read_data_if)::set(null, "*.env*", "r_vif", r_if);
    uvm_config_db#(virtual spi_if)::set(null, "*.env.m_spi_agent*", "vif", spi_if);

    uvm_config_db#(virtual spi_host_fsm_if)::set(null, "*.env", "fast_prescaler_bound_if",
                                                 dut.u_caliptra_ss_spi_host.u_spi_core.fast_prescaler_bound_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

`ifdef FSDB
  final begin
    if ($test$plusargs("dump_waves") || $test$plusargs("waves")) begin
      $fsdbDumpflush();
    end
  end
`endif

  if (SPI_HOST_NUM_CS == 1) begin : gen_single_cs_pt_sva
    `ASSERT(Sck_A,    passthrough_i.passthrough_en -> passthrough_i.sck == cio_sck_o, clk, !rst_n)
    `ASSERT(Sck_En_A, passthrough_i.passthrough_en -> passthrough_i.sck_en == cio_sck_en_o,
            clk, !rst_n)
    `ASSERT(Csb_A,    passthrough_i.passthrough_en -> passthrough_i.csb == cio_csb_o[0], clk, !rst_n)
    `ASSERT(Csb_En_A, passthrough_i.passthrough_en -> passthrough_i.csb_en == cio_csb_en_o[0],
            clk, !rst_n)
    `ASSERT(S_En_A,   passthrough_i.passthrough_en -> passthrough_i.s_en == cio_sd_en_o, clk, !rst_n)
    `ASSERT(Sd_O_A,   passthrough_i.passthrough_en -> passthrough_i.s == cio_sd_o, clk, !rst_n)
  end
  `ASSERT(Sd_I_A, passthrough_i.passthrough_en -> passthrough_o.s == cio_sd_i, clk, !rst_n)

endmodule
