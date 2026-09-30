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

  wire clk, rst_n;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire [3:0]                    si_pulldown;
  wire [3:0]                    so_pulldown;
  wire [3:0]                    sio;

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


  // AXI Sub-interfaces for AXI Agent
  axi_write_request_if  aw_if (.clk_i(clk), .rst_ni(rst_n));
  axi_write_data_if     w_if  (.clk_i(clk), .rst_ni(rst_n));
  axi_write_response_if b_if  (.clk_i(clk), .rst_ni(rst_n));
  axi_read_request_if   ar_if (.clk_i(clk), .rst_ni(rst_n));
  axi_read_data_if      r_if  (.clk_i(clk), .rst_ni(rst_n));
  // Prevent compiler from optimizing away the test package (needed for UVM factory)
  spi_host_base_test dummy_test;

  initial begin
    aw_if.if_mode = dv_utils_pkg::Host;
    w_if.if_mode  = dv_utils_pkg::Host;
    b_if.if_mode  = dv_utils_pkg::Host;
    ar_if.if_mode = dv_utils_pkg::Host;
    r_if.if_mode  = dv_utils_pkg::Host;
  end

  wire [3:0] sd;
  pullup (sd[0]);
  pullup (sd[1]);
  pullup (sd[2]);
  pullup (sd[3]);

  spi_if       spi_if(.rst_n(rst_n), .sio(sd));
  spi_passthrough_if       spi_passthrough_if(.rst_n(rst_n));

  // DUT: Caliptra SS SPI Host unwrapped to match RAL paths exactly
  tlul_pkg::tl_h2d_t tl_h2d;
  tlul_pkg::tl_d2h_t tl_d2h;

  // Simple AXI-to-TLUL Behavioral Bridge
  typedef enum logic [2:0] {
    IDLE,
    WRITE_REQ,
    WRITE_RESP,
    WRITE_DRAIN,
    READ_REQ,
    READ_RESP,
    READ_DRAIN
  } bridge_state_e;

  bridge_state_e bridge_state, bridge_state_next;
  
  logic awready_int, wready_int, bvalid_int, arready_int, rvalid_int;
  logic [31:0] rdata_int;
  logic [31:0] awid_q, arid_q;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      awid_q <= '0;
      arid_q <= '0;
    end else begin
      if (aw_if.awvalid && awready_int) awid_q <= aw_if.awid;
      if (ar_if.arvalid && arready_int) begin
        arid_q    <= ar_if.arid;
      end
    end
  end

  assign aw_if.awready = awready_int;
  assign w_if.wready   = wready_int;
  assign b_if.bvalid   = bvalid_int;
  assign b_if.bresp    = 2'b00;
  assign b_if.bid      = awid_q; // Latched ID
  assign b_if.buser    = '0;
  
  assign ar_if.arready = arready_int;
  assign r_if.rvalid   = rvalid_int;
  assign r_if.rdata    = rdata_int;
  assign r_if.rresp    = 2'b00;
  assign r_if.rid      = arid_q; // Latched ID
  assign r_if.rlast    = rvalid_int; // Single beat
  assign r_if.ruser    = '0;

  logic ar_consumed, aw_consumed, w_consumed;
  logic last_served_read;
  logic read_pending, write_pending;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      bridge_state     <= IDLE;
      ar_consumed      <= 1'b0;
      aw_consumed      <= 1'b0;
      w_consumed       <= 1'b0;
      last_served_read <= 1'b0;
    end else begin
      bridge_state <= bridge_state_next;

      if (bridge_state == READ_REQ && tl_d2h.a_ready) begin
        last_served_read <= 1'b1;
      end else if (bridge_state == WRITE_REQ && tl_d2h.a_ready) begin
        last_served_read <= 1'b0;
      end

      if (arready_int && ar_if.arvalid) begin
        ar_consumed <= 1'b1;
      end else if (!ar_if.arvalid) begin
        ar_consumed <= 1'b0;
      end

      if (awready_int && aw_if.awvalid) begin
        aw_consumed <= 1'b1;
      end else if (!aw_if.awvalid) begin
        aw_consumed <= 1'b0;
      end

      if (wready_int && w_if.wvalid) begin
        w_consumed <= 1'b1;
      end else if (!w_if.wvalid) begin
        w_consumed <= 1'b0;
      end
    end
  end

  always_comb begin
    // Default TLUL H2D
    tl_h2d           = '0;
    tl_h2d.a_source  = 1'b0;
    tl_h2d.d_ready   = 1'b0;

    // Default AXI READY and VALID responses
    awready_int = 1'b0;
    wready_int  = 1'b0;
    bvalid_int  = 1'b0;
    
    arready_int = 1'b0;
    rvalid_int  = 1'b0;
    rdata_int   = 32'b0;

    bridge_state_next = bridge_state;

    case (bridge_state)
      IDLE: begin
        read_pending  = ar_if.arvalid && !ar_consumed;
        write_pending = aw_if.awvalid && !aw_consumed && w_if.wvalid && !w_consumed;

        if (read_pending && write_pending) begin
          if (last_served_read) begin
            bridge_state_next = WRITE_REQ;
          end else begin
            bridge_state_next = READ_REQ;
          end
        end else if (read_pending) begin
          bridge_state_next = READ_REQ;
        end else if (write_pending) begin
          bridge_state_next = WRITE_REQ;
        end
      end

      WRITE_REQ: begin
        tl_h2d.a_valid   = 1'b1;
        tl_h2d.a_opcode  = tlul_pkg::PutFullData;
        tl_h2d.a_address = aw_if.awaddr;
        tl_h2d.a_data    = w_if.wdata[31:0];
        tl_h2d.a_mask    = w_if.wstrb[3:0];
        tl_h2d.a_size    = 2'h2;
        
        if (tl_d2h.a_ready) begin
          awready_int = 1'b1;
          wready_int  = 1'b1;
          bridge_state_next = WRITE_RESP;
        end
      end

      WRITE_RESP: begin
        if (tl_d2h.d_valid) begin
          bvalid_int     = 1'b1;
          if (b_if.bready) begin
            tl_h2d.d_ready = 1'b1;
            bridge_state_next = WRITE_DRAIN;
          end
        end
      end

      WRITE_DRAIN: begin
        bridge_state_next = IDLE;
      end

      READ_REQ: begin
        tl_h2d.a_valid   = 1'b1;
        tl_h2d.a_opcode  = tlul_pkg::Get;
        tl_h2d.a_address = ar_if.araddr;
        tl_h2d.a_mask    = 4'hF;
        tl_h2d.a_size    = 2'h2;
        
        if (tl_d2h.a_ready) begin
          arready_int = 1'b1;
          bridge_state_next = READ_RESP;
        end
      end

      READ_RESP: begin
        if (tl_d2h.d_valid) begin
          rvalid_int     = 1'b1;
          rdata_int      = tl_d2h.d_data;
          if (r_if.rready) begin
            tl_h2d.d_ready = 1'b1;
            bridge_state_next = READ_DRAIN;
          end
        end
      end

      READ_DRAIN: begin
        bridge_state_next = IDLE;
      end
    endcase

    // Generate valid TLUL Integrity ECC bits
    if (tl_h2d.a_valid) begin
      tl_h2d.a_user.instr_type = caliptra_prim_mubi_pkg::MuBi4False;
      tl_h2d.a_user.cmd_intg  = tlul_pkg::get_cmd_intg(tl_h2d);
      tl_h2d.a_user.data_intg = tlul_pkg::get_data_intg(tl_h2d.a_data);
    end
  end

  always @(posedge clk) begin
    if (bridge_state != bridge_state_next) begin
      $display("[BRIDGE %0t] state: %0d -> %0d (awv=%0b, wv=%0b, arv=%0b, a_rdy=%0b, d_vld=%0b, brdy=%0b, rrdy=%0b)",
               $time, bridge_state, bridge_state_next, aw_if.awvalid, w_if.wvalid, ar_if.arvalid, tl_d2h.a_ready, tl_d2h.d_valid, b_if.bready, r_if.rready);
    end
  end

  caliptra_ss_spi_host #(
    .NumCS(SPI_HOST_NUM_CS),
    .CmdDepth(8)
  ) dut (
    .clk_i                (clk),
    .rst_ni               (rst_n),
    .tl_i                 (tl_h2d),
    .tl_o                 (tl_d2h),
    .intg_error_o         (intg_error),
    .cio_sck_o            (cio_sck_o),
    .cio_sck_en_o         (cio_sck_en_o),
    .cio_csb_o            (cio_csb_o),
    .cio_csb_en_o         (cio_csb_en_o),
    .cio_sd_o             (cio_sd_o),
    .cio_sd_en_o          (cio_sd_en_o),
    .cio_sd_i             (cio_sd_i),
    .passthrough_i        (passthrough_i),
    .passthrough_o        (passthrough_o),
    .intr_error_o         (intr_error),
    .intr_spi_event_o     (intr_event)
  );

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
  assign spi_passthrough_if.cio_csb_o    = cio_csb_o[0];
  assign spi_passthrough_if.cio_csb_en_o = cio_csb_en_o[0];
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

  // Instantiate SPI Flash Models
  for (genvar i = 0; i < SPI_HOST_NUM_CS; i++) begin : gen_spi_flash
    spiflash #(
      .FlashSize (1024 * 1024), // 1MB
      .PageSize  (256),         // 256 Bytes
      .EnFastSim (1'b1)         // Fast simulation delays
    ) u_spi_flash (
      .sck (cio_sck_o),
      .csb (cio_csb_o[i]),
      .sd  (sd)
    );
  end

  assign interrupts[SpiHostError] = intr_error;
  assign interrupts[SpiHostEvent] = intr_event;

  // Bind
  bind dut.u_spi_core spi_host_fsm_if fast_prescaler_bound_if();
  spi_host_cov_bind u_spi_host_cov_bind();

  defparam dut.u_reg.u_prim_reg_we_check.u_caliptra_prim_onehot_check.EnableAlertTriggerSVA = 0;

  initial begin
    $fsdbDumpfile("waves.fsdb");
    $fsdbDumpvars(0, tb, "+all");
    $fsdbDumpSVA(0, tb);

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
                                                 dut.u_spi_core.fast_prescaler_bound_if);
    $assertoff(0, tb.dut.u_reg);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  final begin
    $fsdbDumpflush();
  end

  `ASSERT(Sck_A,   passthrough_i.passthrough_en -> passthrough_i.sck == cio_sck_o, clk, !rst_n)
  `ASSERT(Sck_En_A,passthrough_i.passthrough_en -> passthrough_i.sck_en == cio_sck_en_o,
          clk, !rst_n)
  `ASSERT(Csb_A,   passthrough_i.passthrough_en -> passthrough_i.csb == cio_csb_o[0], clk, !rst_n)
  `ASSERT(Csb_En_A,passthrough_i.passthrough_en -> passthrough_i.csb_en == cio_csb_en_o[0],
          clk, !rst_n)
  `ASSERT(S_En_A,  passthrough_i.passthrough_en -> passthrough_i.s_en == cio_sd_en_o, clk, !rst_n)
  `ASSERT(Sd_O_A,  passthrough_i.passthrough_en -> passthrough_i.s == cio_sd_o, clk, !rst_n)
  `ASSERT(Sd_I_A,  passthrough_i.passthrough_en -> passthrough_o.s == cio_sd_i, clk, !rst_n)

endmodule

