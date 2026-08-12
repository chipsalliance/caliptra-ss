// Copyright lowRISC contributors (OpenTitan project).
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
    aw_if.set_user_req_width(0);
    ar_if.set_user_req_width(0);
    w_if.set_user_data_width(0);
    r_if.set_user_data_width(0);
    b_if.set_user_resp_width(0);

    aw_if.set_addr_width(32);
    ar_if.set_addr_width(32);
    w_if.set_data_width(32);
    r_if.set_data_width(32);

    aw_if.if_mode = dv_utils_pkg::Host;
    w_if.if_mode  = dv_utils_pkg::Host;
    b_if.if_mode  = dv_utils_pkg::Host;
    ar_if.if_mode = dv_utils_pkg::Host;
    r_if.if_mode  = dv_utils_pkg::Host;
  end


  spi_if       spi_if(.rst_n(rst_n), .sio(sio));
  spi_passthrough_if       spi_passthrough_if(.rst_n(rst_n));

  // DUT: Caliptra SS SPI Host unwrapped to match RAL paths exactly
  tlul_pkg::tl_h2d_t tl_h2d;
  tlul_pkg::tl_d2h_t tl_d2h;

  // Simple AXI-to-TLUL Behavioral Bridge
  typedef enum logic [2:0] {
    IDLE,
    WRITE_REQ,
    WRITE_RESP,
    READ_REQ,
    READ_RESP
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

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      bridge_state <= IDLE;
    end else begin
      bridge_state <= bridge_state_next;
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
        if (ar_if.arvalid) begin
          bridge_state_next = READ_REQ;
        end else if (aw_if.awvalid && w_if.wvalid) begin
          bridge_state_next = WRITE_REQ;
        end
      end

      WRITE_REQ: begin
        tl_h2d.a_valid   = 1'b1;
        tl_h2d.a_opcode  = (w_if.wstrb[3:0] == 4'hF) ? tlul_pkg::PutFullData : tlul_pkg::PutPartialData;
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
        if (tl_d2h.d_valid && tl_d2h.d_opcode == tlul_pkg::AccessAck) begin
          bvalid_int     = 1'b1;
          if (b_if.bready) begin
            tl_h2d.d_ready = 1'b1;
            bridge_state_next = IDLE;
          end
        end
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
        if (tl_d2h.d_valid && tl_d2h.d_opcode == tlul_pkg::AccessAckData) begin
          rvalid_int     = 1'b1;
          rdata_int      = tl_d2h.d_data;
          if (r_if.rready) begin
            tl_h2d.d_ready = 1'b1;
            bridge_state_next = IDLE;
          end
        end
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
    $display("CYCLE: time=%0t, state=%0d, awv=%0b, wv=%0b, awr=%0b, wr=%0b, bv=%0b, br=%0b, arv=%0b, arr=%0b, rv=%0b, rr=%0b, TL_AV=%0b, TL_AR=%0b, TL_DV=%0b, TL_DR=%0b, AWADDR=0x%0h, WDATA=0x%0h, WSTRB=0x%0h, TL_ADDR=0x%0h, TL_DATA=0x%0h, TL_MASK=0x%0h",
      $time, bridge_state, aw_if.awvalid, w_if.wvalid, awready_int, wready_int, bvalid_int, b_if.bready,
      ar_if.arvalid, arready_int, rvalid_int, r_if.rready,
      tl_h2d.a_valid, tl_d2h.a_ready, tl_d2h.d_valid, tl_h2d.d_ready,
      aw_if.awaddr, w_if.wdata, w_if.wstrb, tl_h2d.a_address, tl_h2d.a_data, tl_h2d.a_mask);
  end

  int watchdog_cnt = 0;
  always @(posedge clk) begin
    if (bridge_state != IDLE) begin
      watchdog_cnt <= watchdog_cnt + 1;
      if (watchdog_cnt > 200) begin
        $fatal(1, "WATCHDOG TIMEOUT: Deadlock detected in state %0d at time %0t", bridge_state, $time);
      end
    end else begin
      watchdog_cnt <= 0;
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
  assign spi_passthrough_if.cio_csb_o    = cio_csb_o;
  assign spi_passthrough_if.cio_csb_en_o = cio_csb_en_o;
  assign spi_passthrough_if.cio_sd_en_o  = cio_sd_en_o;
  assign spi_passthrough_if.cio_sd_o     = cio_sd_o;

  assign cio_sd_i = spi_passthrough_if.passthrough_en ? spi_passthrough_if.cio_sd_i : si_pulldown;

  // configure spi_if i/o
  assign spi_if.sck = (cio_sck_en_o) ? cio_sck_o : 1'bz;
  for (genvar i = 0; i < 4; i++) begin : gen_tri_state
    pullup (weak1) pd_in_i (si_pulldown[i]);
    pullup (weak1) pd_out_i (so_pulldown[i]);
    assign sio[i]  = (cio_sd_en_o[i]) ? cio_sd_o[i] : 'z;
    assign (highz0, pull1) sio[i] = !cio_sd_en_o[i];
    assign si_pulldown[i] = sio[i];

    if (i < SPI_HOST_NUM_CS) begin : gen_drive_csb
      assign spi_if.csb[i] = cio_csb_en_o[i] ? cio_csb_o[i] : 1'b1;
    end
  end
  assign sio[1] = sio[0]; // Hardware Loopback of MOSI to MISO for Smoke Test

  assign interrupts[SpiHostError] = intr_error;
  assign interrupts[SpiHostEvent] = intr_event;

  // Bind
  bind dut.u_spi_core spi_host_fsm_if fast_prescaler_bound_if();

  initial begin
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

  `ASSERT(Sck_A,   passthrough_i.passthrough_en -> passthrough_i.sck == cio_sck_o, clk, !rst_n)
  `ASSERT(Sck_En_A,passthrough_i.passthrough_en -> passthrough_i.sck_en == cio_sck_en_o,
          clk, !rst_n)
  `ASSERT(Csb_A,   passthrough_i.passthrough_en -> passthrough_i.csb == cio_csb_o, clk, !rst_n)
  `ASSERT(Csb_En_A,passthrough_i.passthrough_en -> passthrough_i.csb_en == cio_csb_en_o,
          clk, !rst_n)
  `ASSERT(S_En_A,  passthrough_i.passthrough_en -> passthrough_i.s_en == cio_sd_en_o, clk, !rst_n)
  `ASSERT(Sd_O_A,  passthrough_i.passthrough_en -> passthrough_i.s == cio_sd_o, clk, !rst_n)
  `ASSERT(Sd_I_A,  passthrough_i.passthrough_en -> passthrough_o.s == cio_sd_i, clk, !rst_n)

`ifdef VCS_DEBUG
  initial begin
     $fsdbDumpfile("dump.fsdb");
     $fsdbDumpvars(0, tb);
     $fsdbDumpMDA(0, tb);
  end
`endif

  initial begin
    $monitor("DUT_MON: time=%0t, rst_n=%b, txempty=%b, rxempty=%b, ready=%b, sw_rst=%b, spien=%b, cmdqd=%b, under_rst=%b", 
      $time, rst_n, dut.tx_empty, dut.rx_empty, dut.u_spi_core.command_ready_o, 
      dut.reg2hw.control.sw_rst.q, dut.reg2hw.control.spien.q, dut.hw2reg.status.cmdqd.d,
      dut.u_cmd_queue.cmd_fifo.gen_normal_fifo.under_rst);
  end

endmodule
