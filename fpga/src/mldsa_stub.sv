
//Initial top level module

module mldsa_top
  #(
  //top level params
    parameter AHB_ADDR_WIDTH = 32,
    parameter AHB_DATA_WIDTH = 64,
    parameter CLIENT_DATA_WIDTH = 32
  )
  (
  input logic clk,
  input logic rst_b,

  //ahb input
  input logic  [AHB_ADDR_WIDTH-1:0] haddr_i,
  input logic  [AHB_DATA_WIDTH-1:0] hwdata_i,
  input logic                       hsel_i,
  input logic                       hwrite_i,
  input logic                       hready_i,
  input logic  [1:0]                htrans_i,
  input logic  [2:0]                hsize_i,

  //ahb output
  output logic                      hresp_o,
  output logic                      hreadyout_o,
  output logic [AHB_DATA_WIDTH-1:0] hrdata_o,

  output logic                      error_intr,
  output logic                      notif_intr


  );
// Drive zero on output signals
assign hresp_o = 0;
assign hreadyout_o = 0;
assign hrdata_o = 0;
assign error_intr = 0;
assign notif_intr = 0;

  endmodule
  