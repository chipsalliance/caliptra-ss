// Macros for ICache

`define EL2_IC_TAG_PACKED_SRAM(depth, width, export_if)                                                     \
   ram_be_``depth``x``width  ic_way_tag (                                                                   \
      .CLK (``export_if``.clk),                                                                             \
      .ME  (|``export_if``.ic_tag_clken_final),                                                             \
      .WE  (|``export_if``.ic_tag_wren_q[pt.ICACHE_NUM_WAYS-1:0]),                                          \
      .WEM (``export_if``.ic_tag_wren_biten_vec[``width-1:0]),                                              \
                                                                                                            \
      .D   ({pt.ICACHE_NUM_WAYS{``export_if``.ic_tag_wr_data[``width/pt.ICACHE_NUM_WAYS-1:0]}}),            \
      .ADR (``export_if``.ic_rw_addr_q[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO]),                         \
      .Q   (``export_if``.ic_tag_data_raw_packed_pre[``width-1:0]),                                         \
      .ROP ( ),                                                                                             \
                                                                                                            \
      .TEST1    (1'b0),                                                                                     \
      .RME      (1'b0),                                                                                     \
      .RM       (4'b0000),                                                                                  \
                                                                                                            \
      .LS       (1'b0),                                                                                     \
      .DS       (1'b0),                                                                                     \
      .SD       (1'b0),                                                                                     \
                                                                                                            \
      .TEST_RNM (1'b0),                                                                                     \
      .BC1      (1'b0),                                                                                     \
      .BC2      (1'b0)                                                                                      \
   );


`define EL2_IC_TAG_SRAM(depth, width, i, export_if)                                             \
   ram_``depth``x``width  ic_way_tag (                                                          \
      .CLK (``export_if``.clk),                                                                 \
      .ME(``export_if``.ic_tag_clken_final[i]),                                                 \
      .WE (``export_if``.ic_tag_wren_q[i]),                                                     \
      .D  (``export_if``.ic_tag_wr_data[``width-1:0]),                                          \
      .ADR(``export_if``.ic_rw_addr_q[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO]),              \
      .Q  (``export_if``.ic_tag_data_raw_pre[i][``width-1:0]),                                  \
      .ROP ( ),                                                                                 \
                                                                                                \
      .TEST1    (1'b0),                                                                         \
      .RME      (1'b0),                                                                         \
      .RM       (4'b0000),                                                                      \
                                                                                                \
      .LS       (1'b0),                                                                         \
      .DS       (1'b0),                                                                         \
      .SD       (1'b0),                                                                         \
                                                                                                \
      .TEST_RNM (1'b0),                                                                         \
      .BC1      (1'b0),                                                                         \
      .BC2      (1'b0)                                                                          \
   );


`define EL2_PACKED_IC_DATA_SRAM(depth, width, waywidth, k, export_if)                                    \
    ram_be_``depth``x``width  ic_bank_sb_way_data (                                                      \
      .CLK   (``export_if``.clk),                                                                        \
      .WE    (|``export_if``.ic_b_sb_wren[k]),                                                           \
      .WEM   (``export_if``.ic_b_sb_bit_en_vec[k]),                                                      \
      .D     ({pt.ICACHE_NUM_WAYS{``export_if``.ic_sb_wr_data[k][``waywidth-1:0]}}),                     \
      .ADR   (``export_if``.ic_rw_addr_bank_q[k][pt.ICACHE_INDEX_HI:pt.ICACHE_DATA_INDEX_LO]),           \
      .Q     (``export_if``.wb_packeddout_pre[k]),                                                       \
      .ME    (|``export_if``.ic_bank_way_clken_final[k]),                                                \
      .ROP   ( ),                                                                                        \
      .TEST1 (1'b0),                                                                                     \
      .RME   (1'b0),                                                                                     \
      .RM    (4'b0000),                                                                                  \
                                                                                                         \
      .LS    (1'b0),                                                                                     \
      .DS    (1'b0),                                                                                     \
      .SD    (1'b0),                                                                                     \
                                                                                                         \
      .TEST_RNM (1'b0),                                                                                  \
      .BC1      (1'b0),                                                                                  \
      .BC2      (1'b0)                                                                                   \
   );


`define EL2_IC_DATA_SRAM(depth, width, i, k, export_if)                                                \
   ram_``depth``x``width ic_bank_sb_way_data (                                                         \
      .CLK (``export_if``.clk),                                                                        \
      .ME  (``export_if``.ic_bank_way_clken_final_up[i][k]),                                           \
      .WE  (``export_if``.ic_b_sb_wren[k][i]),                                                         \
      .D   (``export_if``.ic_sb_wr_data[k][``width-1:0]),                                              \
      .ADR (``export_if``.ic_rw_addr_bank_q[k][pt.ICACHE_INDEX_HI:pt.ICACHE_DATA_INDEX_LO]),           \
      .Q   (``export_if``.wb_dout_pre_up[i][k]),                                                       \
      .ROP ( ),                                                                                       \
      .TEST1   (1'b0),                                                                                \
      .RME     (1'b0),                                                                                \
      .RM      (4'b0000),                                                                             \
                                                                                                      \
      .LS       (1'b0),                                                                               \
      .DS       (1'b0),                                                                               \
      .SD       (1'b0),                                                                               \
                                                                                                      \
      .TEST_RNM (1'b0),                                                                               \
      .BC1      (1'b0),                                                                               \
      .BC2      (1'b0)                                                                                \
   );
