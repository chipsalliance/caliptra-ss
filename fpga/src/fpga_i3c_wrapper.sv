// SPDX-License-Identifier: Apache-2.0
`include "i3c_defines.svh"

module fpga_i3c_wrapper #(
    parameter int unsigned AxiDataWidth = `AXI_DATA_WIDTH,
    parameter int unsigned AxiAddrWidth = `AXI_ADDR_WIDTH,
    parameter int unsigned AxiUserWidth = `AXI_USER_WIDTH,
    parameter int unsigned AxiIdWidth = `AXI_ID_WIDTH,
    parameter int unsigned DatAw = i3c_pkg::DatAw,
    parameter int unsigned DctAw = i3c_pkg::DctAw,

    parameter int unsigned CsrAddrWidth = I3CCSR_pkg::I3CCSR_MIN_ADDR_WIDTH,
    parameter int unsigned CsrDataWidth = I3CCSR_pkg::I3CCSR_DATA_WIDTH
) (
    input clk_i,  // clock
    input rst_ni, // active low reset

    // AXI4 Interface
    // AXI Read Channels
    input  logic [AxiAddrWidth-1:0] araddr_i,
    input  logic [             1:0] arburst_i,
    input  logic [             2:0] arsize_i,
    input  logic [             7:0] arlen_i,
    input  logic [AxiUserWidth-1:0] aruser_i,
    input  logic [  AxiIdWidth-1:0] arid_i,
    input  logic                    arlock_i,
    input  logic                    arvalid_i,
    output logic                    arready_o,

    output logic [AxiDataWidth-1:0] rdata_o,
    output logic [             1:0] rresp_o,
    output logic [  AxiIdWidth-1:0] rid_o,
    output logic                    rlast_o,
    output logic                    rvalid_o,
    input  logic                    rready_i,

    // AXI Write Channels
    input  logic [AxiAddrWidth-1:0] awaddr_i,
    input  logic [             1:0] awburst_i,
    input  logic [             2:0] awsize_i,
    input  logic [             7:0] awlen_i,
    input  logic [AxiUserWidth-1:0] awuser_i,
    input  logic [  AxiIdWidth-1:0] awid_i,
    input  logic                    awlock_i,
    input  logic                    awvalid_i,
    output logic                    awready_o,

    input  logic [  AxiDataWidth-1:0] wdata_i,
    input  logic [AxiDataWidth/8-1:0] wstrb_i,
    input  logic                      wlast_i,
    input  logic                      wvalid_i,
    output logic                      wready_o,

    output logic [           1:0] bresp_o,
    output logic [AxiIdWidth-1:0] bid_o,
    output logic                  bvalid_o,
    input  logic                  bready_i,

    // Signals to pmod-i3c-driver board
    // Discrete
    output logic SDA_UP,
    output logic SDA_PUSH,
    output logic SDA_PULL,
    input  logic SDA,
    output logic SCL_UP,
    output logic SCL_PUSH,
    output logic SCL_PULL,
    input  logic SCL,

    // Recovery interface signals
    output logic recovery_payload_available_o,
    output logic recovery_image_activated_o
);

  // DAT memory export interface
  i3c_pkg::dat_mem_src_t dat_mem_src;
  i3c_pkg::dat_mem_sink_t dat_mem_sink;

  // DCT memory export interface
  i3c_pkg::dct_mem_src_t dct_mem_src;
  i3c_pkg::dct_mem_sink_t dct_mem_sink;

  logic scl_phy2io;
  logic sda_phy2io;
  logic scl_io2phy;
  logic sda_io2phy;
  logic sel_od_pp;


  i3c #(
      .CsrDataWidth(CsrDataWidth),
      .CsrAddrWidth(CsrAddrWidth),
      .DatAw(DatAw),
      .DctAw(DctAw)
  ) i3c (
      .clk_i,
      .rst_ni,

      // AXI Read Channels
      .araddr_i(araddr_i),
      .arburst_i(arburst_i),
      .arsize_i(arsize_i),
      .arlen_i(arlen_i),
      .aruser_i(aruser_i),
      .arid_i(arid_i),
      .arlock_i(arlock_i),
      .arvalid_i(arvalid_i),
      .arready_o(arready_o),

      .rdata_o(rdata_o),
      .rresp_o(rresp_o),
      .rid_o(rid_o),
      .rlast_o(rlast_o),
      .rvalid_o(rvalid_o),
      .rready_i(rready_i),

      // AXI Write Channels
      .awaddr_i(awaddr_i),
      .awburst_i(awburst_i),
      .awsize_i(awsize_i),
      .awlen_i(awlen_i),
      .awuser_i(awuser_i),
      .awid_i(awid_i),
      .awlock_i(awlock_i),
      .awvalid_i(awvalid_i),
      .awready_o(awready_o),

      .wdata_i (wdata_i),
      .wstrb_i (wstrb_i),
      .wlast_i (wlast_i),
      .wvalid_i(wvalid_i),
      .wready_o(wready_o),

      .bresp_o(bresp_o),
      .bid_o(bid_o),
      .bvalid_o(bvalid_o),
      .bready_i(bready_i),

      .i3c_scl_i  (scl_io2phy),
      .i3c_scl_o  (scl_phy2io),
      .i3c_sda_i  (sda_io2phy),
      .i3c_sda_o  (sda_phy2io),
      .sel_od_pp_o(sel_od_pp),

      .dat_mem_src_i (dat_mem_src),
      .dat_mem_sink_o(dat_mem_sink),

      .dct_mem_src_i (dct_mem_src),
      .dct_mem_sink_o(dct_mem_sink),

      .recovery_payload_available_o(recovery_payload_available_o),
      .recovery_image_activated_o  (recovery_image_activated_o)
  );

  prim_ram_1p_adv #(
      .Depth(`DAT_DEPTH),
      .Width(64),
      .DataBitsPerMask(32)
  ) dat_memory (
      .clk_i,
      .rst_ni,
      .req_i(dat_mem_sink.req),
      .write_i(dat_mem_sink.write),
      .addr_i(dat_mem_sink.addr),
      .wdata_i(dat_mem_sink.wdata),
      .wmask_i(dat_mem_sink.wmask),
      .rdata_o(dat_mem_src.rdata),
      .rvalid_o(dat_mem_src.rvalid),  // Unused
      .rerror_o(dat_mem_src.rerror),  // Unused
      .cfg_i('0)  // Unused
  );

  prim_ram_1p_adv #(
      .Depth(`DCT_DEPTH),
      .Width(128),
      .DataBitsPerMask(32)
  ) dct_memory (
      .clk_i,
      .rst_ni,
      .req_i(dct_mem_sink.req),
      .write_i(dct_mem_sink.write),
      .addr_i(dct_mem_sink.addr),
      .wdata_i(dct_mem_sink.wdata),
      .wmask_i(dct_mem_sink.wmask),
      .rdata_o(dct_mem_src.rdata),
      .rvalid_o(dct_mem_src.rvalid),  // Unused
      .rerror_o(dct_mem_src.rerror),  // Unused
      .cfg_i('0)  // Unused
  );


/*
  Line Driver logic
  sel_od_pp == 1 indicates push-pull
  | sel_od_pp | phy2io | phy_data_io |    |   IN |   EN | UP |    |      wire      |
  |         0 |      0 |           z | -> |    x |    1 |  1 | -> | z              | // TODO: Use z or pull up 2k?
  |         0 |      1 |           0 | -> |    1 |    0 |  0 | -> | open drain low |
  |         1 |      0 |           0 | -> |    1 |    0 |  1 | -> | push pull low  |
  |         1 |      1 |           1 | -> |    0 |    0 |  1 | -> | push pull high |
*/

/*
  Discrete logic
  sel_od_pp == 1 indicates push-pull
  | sel_od_pp | phy2io | phy_data_io |    | PUSH | PULL | UP |    |      wire      |
  |         0 |      0 |           z | -> |    1 |    0 |  1 | -> | z              | // TODO: Use z or pull up 2k?
  |         0 |      1 |           0 | -> |    1 |    1 |  0 | -> | open drain low |
  |         1 |      0 |           0 | -> |    1 |    1 |  1 | -> | push pull low  |
  |         1 |      1 |           1 | -> |    0 |    0 |  1 | -> | push pull high |
*/
  assign scl_io2phy = SCL;
  assign sda_io2phy = SDA;

  always_comb begin
    case ({
      sel_od_pp, scl_phy2io
    })
      2'b00:   {SCL_PUSH, SCL_PULL, SCL_UP} = 3'b101;
      2'b01:   {SCL_PUSH, SCL_PULL, SCL_UP} = 3'b110;
      2'b10:   {SCL_PUSH, SCL_PULL, SCL_UP} = 3'b111;
      2'b11:   {SCL_PUSH, SCL_PULL, SCL_UP} = 3'b001;
      default: {SCL_PUSH, SCL_PULL, SCL_UP} = 3'b101;
    endcase
  end

  always_comb begin
    case ({
      sel_od_pp, sda_phy2io
    })
      2'b00:   {SDA_PUSH, SDA_PULL, SDA_UP} = 3'b101;
      2'b01:   {SDA_PUSH, SDA_PULL, SDA_UP} = 3'b110;
      2'b10:   {SDA_PUSH, SDA_PULL, SDA_UP} = 3'b111;
      2'b11:   {SDA_PUSH, SDA_PULL, SDA_UP} = 3'b001;
      default: {SDA_PUSH, SDA_PULL, SDA_UP} = 3'b101;
    endcase
  end

endmodule
