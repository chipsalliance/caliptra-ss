module mcu_el2_btb_tag_hash
import mcu_el2_pkg::*;
#(
`include "mcu_el2_param.vh"
 ) (
                       input logic [mcu_pt.BTB_ADDR_HI+mcu_pt.BTB_BTAG_SIZE+mcu_pt.BTB_BTAG_SIZE+mcu_pt.BTB_BTAG_SIZE:mcu_pt.BTB_ADDR_HI+1] pc,
                       output logic [mcu_pt.BTB_BTAG_SIZE-1:0] hash
                       );

    assign hash = {(pc[mcu_pt.BTB_ADDR_HI+mcu_pt.BTB_BTAG_SIZE+mcu_pt.BTB_BTAG_SIZE+mcu_pt.BTB_BTAG_SIZE:mcu_pt.BTB_ADDR_HI+mcu_pt.BTB_BTAG_SIZE+mcu_pt.BTB_BTAG_SIZE+1] ^
                   pc[mcu_pt.BTB_ADDR_HI+mcu_pt.BTB_BTAG_SIZE+mcu_pt.BTB_BTAG_SIZE:mcu_pt.BTB_ADDR_HI+mcu_pt.BTB_BTAG_SIZE+1] ^
                   pc[mcu_pt.BTB_ADDR_HI+mcu_pt.BTB_BTAG_SIZE:mcu_pt.BTB_ADDR_HI+1])};
endmodule

module mcu_el2_btb_tag_hash_fold
import mcu_el2_pkg::*;
#(
`include "mcu_el2_param.vh"
 )(
                       input logic [mcu_pt.BTB_ADDR_HI+mcu_pt.BTB_BTAG_SIZE+mcu_pt.BTB_BTAG_SIZE:mcu_pt.BTB_ADDR_HI+1] pc,
                       output logic [mcu_pt.BTB_BTAG_SIZE-1:0] hash
                       );

    assign hash = {(
                   pc[mcu_pt.BTB_ADDR_HI+mcu_pt.BTB_BTAG_SIZE+mcu_pt.BTB_BTAG_SIZE:mcu_pt.BTB_ADDR_HI+mcu_pt.BTB_BTAG_SIZE+1] ^
                   pc[mcu_pt.BTB_ADDR_HI+mcu_pt.BTB_BTAG_SIZE:mcu_pt.BTB_ADDR_HI+1])};

endmodule

module mcu_el2_btb_addr_hash
import mcu_el2_pkg::*;
#(
`include "mcu_el2_param.vh"
 )(
                        input logic [mcu_pt.BTB_INDEX3_HI:mcu_pt.BTB_INDEX1_LO] pc,
                        output logic [mcu_pt.BTB_ADDR_HI:mcu_pt.BTB_ADDR_LO] hash
                        );


if(mcu_pt.BTB_FOLD2_INDEX_HASH) begin : fold2
   assign hash[mcu_pt.BTB_ADDR_HI:mcu_pt.BTB_ADDR_LO] = pc[mcu_pt.BTB_INDEX1_HI:mcu_pt.BTB_INDEX1_LO] ^
                                                pc[mcu_pt.BTB_INDEX3_HI:mcu_pt.BTB_INDEX3_LO];
end
   else begin
   assign hash[mcu_pt.BTB_ADDR_HI:mcu_pt.BTB_ADDR_LO] = pc[mcu_pt.BTB_INDEX1_HI:mcu_pt.BTB_INDEX1_LO] ^
                                                pc[mcu_pt.BTB_INDEX2_HI:mcu_pt.BTB_INDEX2_LO] ^
                                                pc[mcu_pt.BTB_INDEX3_HI:mcu_pt.BTB_INDEX3_LO];
end

endmodule

module mcu_el2_btb_ghr_hash
import mcu_el2_pkg::*;
#(
`include "mcu_el2_param.vh"
 )(
                       input logic [mcu_pt.BTB_ADDR_HI:mcu_pt.BTB_ADDR_LO] hashin,
                       input logic [mcu_pt.BHT_GHR_SIZE-1:0] ghr,
                       output logic [mcu_pt.BHT_ADDR_HI:mcu_pt.BHT_ADDR_LO] hash
                       );

   // The hash function is too complex to write in verilog for all cases.
   // The config script generates the logic string based on the bp config.
   if(mcu_pt.BHT_GHR_HASH_1) begin : ghrhash_cfg1
     assign hash[mcu_pt.BHT_ADDR_HI:mcu_pt.BHT_ADDR_LO] = { ghr[mcu_pt.BHT_GHR_SIZE-1:mcu_pt.BTB_INDEX1_HI-1], hashin[mcu_pt.BTB_INDEX1_HI:2]^ghr[mcu_pt.BTB_INDEX1_HI-2:0]};
   end
   else begin : ghrhash_cfg2
     assign hash[mcu_pt.BHT_ADDR_HI:mcu_pt.BHT_ADDR_LO] = { hashin[mcu_pt.BHT_GHR_SIZE+1:2]^ghr[mcu_pt.BHT_GHR_SIZE-1:0]};
   end


endmodule
