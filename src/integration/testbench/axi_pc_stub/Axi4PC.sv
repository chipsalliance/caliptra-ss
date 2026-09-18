/* synthesis translate_off */
`ifndef AXI4PC_SV
`define AXI4PC_SV
// Minimal stub of Arm Axi4PC to satisfy filelists for Verilator.
// Add/remove parameters/ports only if your build complains.
module Axi4PC #(
  parameter int ADDR_WIDTH = 32,
  parameter int DATA_WIDTH = 64,
  parameter int ID_WIDTH   = 4,
  parameter bit HAS_BURST  = 1
)(
  input  logic           ACLK,
  input  logic           ARESETn
  // ... leave unconnected; instances will ignore in Verilator
);
  // No functionality for Verilator builds
endmodule
`endif
/* synthesis translate_on */
