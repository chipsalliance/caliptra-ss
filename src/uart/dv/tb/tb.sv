// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import uart_env_pkg::*;
  import uart_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire intr_tx_watermark;
  wire intr_tx_empty;
  wire intr_rx_watermark;
  wire intr_tx_done;
  wire intr_rx_overflow;
  wire intr_rx_frame_err;
  wire intr_rx_break_err;
  wire intr_rx_timeout;
  wire intr_rx_parity_err;
  wire intg_error;
  wire uart_rx, uart_tx, uart_tx_en;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if clk_rst_if(.clk, .rst_n);
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) intg_error_if(intg_error);

  axi_if #(
    .AW(32),
    .DW(32),
    .IW(top_pkg::TL_AIW),
    .UW(32)
  ) axi_if (
    .clk(clk),
    .rst_n(rst_n)
  );

  axi_write_request_if  axi_write_req_if(.clk_i(clk), .rst_ni(rst_n));
  axi_write_data_if     axi_write_dat_if(.clk_i(clk), .rst_ni(rst_n));
  axi_write_response_if axi_write_rsp_if(.clk_i(clk), .rst_ni(rst_n));
  axi_read_request_if   axi_read_req_if(.clk_i(clk), .rst_ni(rst_n));
  axi_read_data_if      axi_read_dat_if(.clk_i(clk), .rst_ni(rst_n));

  // Connect AXI channel interfaces to axi_if
  assign axi_if.awvalid = axi_write_req_if.awvalid;
  assign axi_write_req_if.awready = axi_if.awready;
  assign axi_if.awaddr = axi_write_req_if.awaddr;
  assign axi_if.awid = axi_write_req_if.awid;
  assign axi_if.awlen = axi_write_req_if.awlen;
  assign axi_if.awsize = axi_write_req_if.awsize;
  assign axi_if.awlock = axi_write_req_if.awlock;
  assign axi_if.awuser = axi_write_req_if.awuser;

  assign axi_if.wvalid = axi_write_dat_if.wvalid;
  assign axi_write_dat_if.wready = axi_if.wready;
  assign axi_if.wdata = axi_write_dat_if.wdata;
  assign axi_if.wstrb = axi_write_dat_if.wstrb;
  assign axi_if.wlast = axi_write_dat_if.wlast;
  assign axi_if.wuser = axi_write_dat_if.wuser;

  assign axi_write_rsp_if.bvalid = axi_if.bvalid;
  assign axi_if.bready = axi_write_rsp_if.bready;
  assign axi_write_rsp_if.bid = axi_if.bid;
  assign axi_write_rsp_if.bresp = axi_if.bresp;
  assign axi_write_rsp_if.buser = axi_if.buser;

  assign axi_if.arvalid = axi_read_req_if.arvalid;
  assign axi_read_req_if.arready = axi_if.arready;
  assign axi_if.araddr = axi_read_req_if.araddr;
  assign axi_if.arid = axi_read_req_if.arid;
  assign axi_if.arlen = axi_read_req_if.arlen;
  assign axi_if.arsize = axi_read_req_if.arsize;
  assign axi_if.arlock = axi_read_req_if.arlock;
  assign axi_if.aruser = axi_read_req_if.aruser;

  assign axi_read_dat_if.rvalid = axi_if.rvalid;
  assign axi_if.rready = axi_read_dat_if.rready;
  assign axi_read_dat_if.rid = axi_if.rid;
  assign axi_read_dat_if.rdata = axi_if.rdata;
  assign axi_read_dat_if.rresp = axi_if.rresp;
  assign axi_read_dat_if.rlast = axi_if.rlast;
  assign axi_read_dat_if.ruser = axi_if.ruser;

  uart_if uart_if();
  uart_nf_if uart_nf_if(.clk_i(clk), .rst_ni(rst_n));

  // DUT: Caliptra SS UART AXI wrapper
  uart_axi #(
    .AxiAw(32),
    .AxiDw(32),
    .AxiUw(32),
    .AxiIw(top_pkg::TL_AIW)
  ) dut (
    .clk_i                (clk        ),
    .rst_ni               (rst_n      ),

    // AXI i/f
    .s_axi_w_if           (axi_if.w_sub),
    .s_axi_r_if           (axi_if.r_sub),

//    .intg_error_o         (intg_error ),

    .cio_rx_i             (uart_rx    ),
    .cio_tx_o             (uart_tx    ),
    .cio_tx_en_o          (uart_tx_en ),

    .intr_tx_watermark_o  (intr_tx_watermark ),
    .intr_tx_empty_o      (intr_tx_empty     ),
    .intr_rx_watermark_o  (intr_rx_watermark ),
    .intr_tx_done_o       (intr_tx_done      ),
    .intr_rx_overflow_o   (intr_rx_overflow  ),
    .intr_rx_frame_err_o  (intr_rx_frame_err ),
    .intr_rx_break_err_o  (intr_rx_break_err ),
    .intr_rx_timeout_o    (intr_rx_timeout   ),
    .intr_rx_parity_err_o (intr_rx_parity_err)
  );

  assign interrupts[TxWatermark] = intr_tx_watermark;
  assign interrupts[TxEmpty]     = intr_tx_empty;
  assign interrupts[RxWatermark] = intr_rx_watermark;
  assign interrupts[TxDone]      = intr_tx_done;
  assign interrupts[RxOverflow]  = intr_rx_overflow;
  assign interrupts[RxFrameErr]  = intr_rx_frame_err;
  assign interrupts[RxBreakErr]  = intr_rx_break_err;
  assign interrupts[RxTimeout]   = intr_rx_timeout;
  assign interrupts[RxParityErr] = intr_rx_parity_err;

  assign uart_rx = uart_if.uart_rx;
  assign uart_if.uart_tx = uart_tx;

  assign uart_nf_if.rx_sync    = dut.u_caliptra_ss_uart.caliptra_ss_uart_core.rx_sync;
  assign uart_nf_if.rx_sync_q1 = dut.u_caliptra_ss_uart.caliptra_ss_uart_core.rx_sync_q1;
  assign uart_nf_if.rx_sync_q2 = dut.u_caliptra_ss_uart.caliptra_ss_uart_core.rx_sync_q2;
  assign uart_nf_if.rx_enable  = dut.u_caliptra_ss_uart.caliptra_ss_uart_core.rx_enable;
  assign dut.u_caliptra_ss_uart.u_reg.u_prim_reg_we_check.u_caliptra_prim_onehot_check.unused_assert_connected = 1'b1;

  // TB-only helper: correctly update pending_txn at clock edges without touching RTL
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      force dut.u_axi2tlul_uart.i_sub2tlul.pending_txn = 1'b0;
    end else begin
      if (dut.u_axi2tlul_uart.i_sub2tlul.tl_i.d_valid) begin
        force dut.u_axi2tlul_uart.i_sub2tlul.pending_txn = 1'b0;
      end else if (dut.u_axi2tlul_uart.i_sub2tlul.dv && dut.u_axi2tlul_uart.i_sub2tlul.tl_i.a_ready) begin
        force dut.u_axi2tlul_uart.i_sub2tlul.pending_txn = 1'b1;
      end
    end
  end

  initial begin
    // drive clk and rst_n from clk_if
    axi_write_req_if.if_mode = dv_utils_pkg::Host;
    axi_write_dat_if.if_mode = dv_utils_pkg::Host;
    axi_write_rsp_if.if_mode = dv_utils_pkg::Host;
    axi_read_req_if.if_mode  = dv_utils_pkg::Host;
    axi_write_req_if.set_id_w_width(top_pkg::TL_AIW);
    axi_write_rsp_if.set_id_w_width(top_pkg::TL_AIW);
    axi_write_req_if.set_addr_width(32);
    axi_write_dat_if.set_user_data_width(0);
    axi_write_dat_if.set_data_width(32);
    axi_read_req_if.set_id_r_width(top_pkg::TL_AIW);
    axi_read_req_if.set_user_req_width(32);
    axi_read_dat_if.set_id_r_width(top_pkg::TL_AIW);
    axi_read_req_if.set_addr_width(32);
    axi_read_dat_if.set_user_data_width(0);
    axi_read_dat_if.set_data_width(32);
    axi_read_dat_if.if_mode  = dv_utils_pkg::Host;
    clk_rst_if.set_active();
    clk_rst_if.drive_rst_pin(1'b1);
    clk_rst_if.start_clk();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual pins_if #(1))::set(null, "*.env", "intg_error_vif", intg_error_if);

    uvm_config_db#(virtual axi_write_request_if)::set(null, "*", "write_request_vif", axi_write_req_if);
    uvm_config_db#(virtual axi_write_data_if)::set(null, "*", "write_data_vif", axi_write_dat_if);
    uvm_config_db#(virtual axi_write_response_if)::set(null, "*", "write_response_vif", axi_write_rsp_if);
    uvm_config_db#(virtual axi_read_request_if)::set(null, "*", "read_request_vif", axi_read_req_if);
    uvm_config_db#(virtual axi_read_data_if)::set(null, "*", "read_data_vif", axi_read_dat_if);

    uvm_config_db#(virtual uart_if)::set(null, "*.env.m_uart_agent*", "vif", uart_if);
    uvm_config_db#(virtual uart_nf_if)::set(null, "*.scoreboard", "uart_nf_vif", uart_nf_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

`ifdef VCS_DEBUG
  initial begin
     $fsdbDumpfile("dump.fsdb");
     $fsdbDumpvars(0, tb);
     $fsdbDumpMDA(0, tb);
  end
`endif

  // we expect the output enable to be always 1
  `ASSERT(UartTxEnTiedTo1_A, uart_tx_en, clk, !rst_n)

endmodule
