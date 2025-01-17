module mci_sram #(
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

  localparam NUM_BYTES = DATA_WIDTH/8 + ((DATA_WIDTH % 8) ? 1 : 0);

  bit [ 7:0] mem[0:DEPTH-1];
  bit [ 6:0] ecc[0:(DEPTH/4)-1];

  always @(posedge clk_i) begin
    if (cs_i & we_i) begin
        ecc[addr_i]           <= wdata_i[38:32];
      { mem[(addr_i)+3],
        mem[(addr_i)+2],
        mem[(addr_i)+1],
        mem[(addr_i)]    } <= wdata_i[31:0];
    end
    if (cs_i & ~we_i) begin
      rdata_o[38:32] <=     ecc[addr_i];
      rdata_o[31:0]  <=  {  mem[(addr_i)+3],
                            mem[(addr_i)+2],
                            mem[(addr_i)+1],
                            mem[(addr_i)]    };
    end
  end

endmodule
