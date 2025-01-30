module caliptra_ss_sram #(
   parameter DEPTH      = 64
  ,parameter DATA_WIDTH = 32
  ,parameter ADDR_WIDTH = $clog2(DEPTH)
) (
  input  logic                       clk_i,
  input  logic                       cs_i,
  input  logic                       we_i,
  input  logic [ADDR_WIDTH-1:0]      addr_i,
  input  logic [DATA_WIDTH-1:0]      wdata_i,
  output logic [DATA_WIDTH-1:0]      rdata_o
);


  bit [ DATA_WIDTH-1:0] ram[0:DEPTH-1];

  always @(posedge clk_i) begin
    if (cs_i & we_i) begin
      ram[addr_i] <= wdata_i;
    end
    if (cs_i & ~we_i) begin
      rdata_o <= ram[addr_i];
    end
  end

endmodule
