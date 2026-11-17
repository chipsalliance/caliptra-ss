// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or it's affiliates.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`define css_mcu0_EL2_LOCAL_RAM_TEST_IO          \
input logic WE,              \
input logic ME,              \
input logic CLK,             \
input logic TEST1,           \
input logic RME,             \
input logic  [3:0] RM,       \
input logic LS,              \
input logic DS,              \
input logic SD,              \
input logic TEST_RNM,        \
input logic BC1,             \
input logic BC2,             \
output logic ROP

`define css_mcu0_EL2_RAM(depth, width)              \
module css_mcu0_ram_``depth``x``width(               \
   input logic [$clog2(depth)-1:0] ADR,     \
   input logic [(width-1):0] D,             \
   output logic [(width-1):0] Q,            \
    `css_mcu0_EL2_LOCAL_RAM_TEST_IO                 \
);                                          \
reg [(width-1):0] ram_core [(depth-1):0];   \
`ifdef GTLSIM                               \
integer i;                                  \
initial begin                               \
   for (i=0; i<depth; i=i+1)                \
     ram_core[i] = '0;                      \
end                                         \
`endif                                      \
always @(posedge CLK) begin                 \
`ifdef GTLSIM                               \
   if (ME && WE) ram_core[ADR] <= D;        \
`else                                       \
   if (ME && WE) begin ram_core[ADR] <= D; Q <= 'x; end  \
`endif                                      \
   if (ME && ~WE) Q <= ram_core[ADR];       \
end                                         \
assign ROP = ME;                            \
                                            \
endmodule

`define css_mcu0_EL2_RAM_BE(depth, width)           \
module css_mcu0_ram_be_``depth``x``width(            \
   input logic [$clog2(depth)-1:0] ADR,     \
   input logic [(width-1):0] D, WEM,        \
   output logic [(width-1):0] Q,            \
    `css_mcu0_EL2_LOCAL_RAM_TEST_IO                 \
);                                          \
reg [(width-1):0] ram_core [(depth-1):0];   \
`ifdef GTLSIM                               \
integer i;                                  \
initial begin                               \
   for (i=0; i<depth; i=i+1)                \
     ram_core[i] = '0;                      \
end                                         \
`endif                                      \
always @(posedge CLK) begin                 \
`ifdef GTLSIM                               \
   if (ME && WE)       ram_core[ADR] <= D & WEM | ~WEM & ram_core[ADR];      \
`else                                       \
   if (ME && WE) begin ram_core[ADR] <= D & WEM | ~WEM & ram_core[ADR]; Q <= 'x; end  \
`endif                                      \
   if (ME && ~WE) Q <= ram_core[ADR];          \
end                                         \
assign ROP = ME;                            \
                                            \
endmodule

// parameterizable RAM for verilator sims
module css_mcu0_el2_ram #(depth=4096, width=39) (
input logic [$clog2(depth)-1:0] ADR,
input logic [(width-1):0] D,
output logic [(width-1):0] Q,
 `css_mcu0_EL2_LOCAL_RAM_TEST_IO
);
reg [(width-1):0] ram_core [(depth-1):0];

always @(posedge CLK) begin
`ifdef GTLSIM
   if (ME && WE)       ram_core[ADR] <= D;
`else
   if (ME && WE) begin ram_core[ADR] <= D; Q <= 'x; end
`endif
   if (ME && ~WE) Q <= ram_core[ADR];
end
endmodule

//=========================================================================================================================
//=================================== START OF CCM  =======================================================================
//============= Possible sram sizes for a 39 bit wide memory ( 4 bytes + 7 bits ECC ) =====================================
//-------------------------------------------------------------------------------------------------------------------------
/*pragma coverage off*/
`css_mcu0_EL2_RAM(32768, 39)
`css_mcu0_EL2_RAM(16384, 39)
`css_mcu0_EL2_RAM(8192, 39)
`css_mcu0_EL2_RAM(4096, 39)
`css_mcu0_EL2_RAM(3072, 39)
`css_mcu0_EL2_RAM(2048, 39)
`css_mcu0_EL2_RAM(1536, 39)     // need this for the 48KB DCCM option)
`css_mcu0_EL2_RAM(1024, 39)
`css_mcu0_EL2_RAM(768, 39)
`css_mcu0_EL2_RAM(512, 39)
`css_mcu0_EL2_RAM(256, 39)
`css_mcu0_EL2_RAM(128, 39)
`css_mcu0_EL2_RAM(1024, 20)
`css_mcu0_EL2_RAM(512, 20)
`css_mcu0_EL2_RAM(256, 20)
`css_mcu0_EL2_RAM(128, 20)
`css_mcu0_EL2_RAM(64, 20)
`css_mcu0_EL2_RAM(4096, 34)
`css_mcu0_EL2_RAM(2048, 34)
`css_mcu0_EL2_RAM(1024, 34)
`css_mcu0_EL2_RAM(512, 34)
`css_mcu0_EL2_RAM(256, 34)
`css_mcu0_EL2_RAM(128, 34)
`css_mcu0_EL2_RAM(64, 34)
`css_mcu0_EL2_RAM(8192, 68)
`css_mcu0_EL2_RAM(4096, 68)
`css_mcu0_EL2_RAM(2048, 68)
`css_mcu0_EL2_RAM(1024, 68)
`css_mcu0_EL2_RAM(512, 68)
`css_mcu0_EL2_RAM(256, 68)
`css_mcu0_EL2_RAM(128, 68)
`css_mcu0_EL2_RAM(64, 68)
`css_mcu0_EL2_RAM(8192, 71)
`css_mcu0_EL2_RAM(4096, 71)
`css_mcu0_EL2_RAM(2048, 71)
`css_mcu0_EL2_RAM(1024, 71)
`css_mcu0_EL2_RAM(512, 71)
`css_mcu0_EL2_RAM(256, 71)
`css_mcu0_EL2_RAM(128, 71)
`css_mcu0_EL2_RAM(64, 71)
`css_mcu0_EL2_RAM(4096, 42)
`css_mcu0_EL2_RAM(2048, 42)
`css_mcu0_EL2_RAM(1024, 42)
`css_mcu0_EL2_RAM(512, 42)
`css_mcu0_EL2_RAM(256, 42)
`css_mcu0_EL2_RAM(128, 42)
`css_mcu0_EL2_RAM(64, 42)
`css_mcu0_EL2_RAM(4096, 22)
`css_mcu0_EL2_RAM(2048, 22)
`css_mcu0_EL2_RAM(1024, 22)
`css_mcu0_EL2_RAM(512, 22)
`css_mcu0_EL2_RAM(256, 22)
`css_mcu0_EL2_RAM(128, 22)
`css_mcu0_EL2_RAM(64, 22)
`css_mcu0_EL2_RAM(1024, 26)
`css_mcu0_EL2_RAM(4096, 26)
`css_mcu0_EL2_RAM(2048, 26)
`css_mcu0_EL2_RAM(512, 26)
`css_mcu0_EL2_RAM(256, 26)
`css_mcu0_EL2_RAM(128, 26)
`css_mcu0_EL2_RAM(64, 26)
`css_mcu0_EL2_RAM(32, 26)
`css_mcu0_EL2_RAM(32, 22)
`css_mcu0_EL2_RAM_BE(8192, 142)
`css_mcu0_EL2_RAM_BE(4096, 142)
`css_mcu0_EL2_RAM_BE(2048, 142)
`css_mcu0_EL2_RAM_BE(1024, 142)
`css_mcu0_EL2_RAM_BE(512, 142)
`css_mcu0_EL2_RAM_BE(256, 142)
`css_mcu0_EL2_RAM_BE(128, 142)
`css_mcu0_EL2_RAM_BE(64, 142)
`css_mcu0_EL2_RAM_BE(8192, 284)
`css_mcu0_EL2_RAM_BE(4096, 284)
`css_mcu0_EL2_RAM_BE(2048, 284)
`css_mcu0_EL2_RAM_BE(1024, 284)
`css_mcu0_EL2_RAM_BE(512, 284)
`css_mcu0_EL2_RAM_BE(256, 284)
`css_mcu0_EL2_RAM_BE(128, 284)
`css_mcu0_EL2_RAM_BE(64, 284)
`css_mcu0_EL2_RAM_BE(8192, 136)
`css_mcu0_EL2_RAM_BE(4096, 136)
`css_mcu0_EL2_RAM_BE(2048, 136)
`css_mcu0_EL2_RAM_BE(1024, 136)
`css_mcu0_EL2_RAM_BE(512, 136)
`css_mcu0_EL2_RAM_BE(256, 136)
`css_mcu0_EL2_RAM_BE(128, 136)
`css_mcu0_EL2_RAM_BE(64, 136)
`css_mcu0_EL2_RAM_BE(8192, 272)
`css_mcu0_EL2_RAM_BE(4096, 272)
`css_mcu0_EL2_RAM_BE(2048, 272)
`css_mcu0_EL2_RAM_BE(1024, 272)
`css_mcu0_EL2_RAM_BE(512, 272)
`css_mcu0_EL2_RAM_BE(256, 272)
`css_mcu0_EL2_RAM_BE(128, 272)
`css_mcu0_EL2_RAM_BE(64, 272)
`css_mcu0_EL2_RAM_BE(4096, 52)
`css_mcu0_EL2_RAM_BE(2048, 52)
`css_mcu0_EL2_RAM_BE(1024, 52)
`css_mcu0_EL2_RAM_BE(512, 52)
`css_mcu0_EL2_RAM_BE(256, 52)
`css_mcu0_EL2_RAM_BE(128, 52)
`css_mcu0_EL2_RAM_BE(64, 52)
`css_mcu0_EL2_RAM_BE(32, 52)
`css_mcu0_EL2_RAM_BE(4096, 104)
`css_mcu0_EL2_RAM_BE(2048, 104)
`css_mcu0_EL2_RAM_BE(1024, 104)
`css_mcu0_EL2_RAM_BE(512, 104)
`css_mcu0_EL2_RAM_BE(256, 104)
`css_mcu0_EL2_RAM_BE(128, 104)
`css_mcu0_EL2_RAM_BE(64, 104)
`css_mcu0_EL2_RAM_BE(32, 104)
`css_mcu0_EL2_RAM_BE(4096, 44)
`css_mcu0_EL2_RAM_BE(2048, 44)
`css_mcu0_EL2_RAM_BE(1024, 44)
`css_mcu0_EL2_RAM_BE(512, 44)
`css_mcu0_EL2_RAM_BE(256, 44)
`css_mcu0_EL2_RAM_BE(128, 44)
`css_mcu0_EL2_RAM_BE(64, 44)
`css_mcu0_EL2_RAM_BE(32, 44)
`css_mcu0_EL2_RAM_BE(4096, 88)
`css_mcu0_EL2_RAM_BE(2048, 88)
`css_mcu0_EL2_RAM_BE(1024, 88)
`css_mcu0_EL2_RAM_BE(512, 88)
`css_mcu0_EL2_RAM_BE(256, 88)
`css_mcu0_EL2_RAM_BE(128, 88)
`css_mcu0_EL2_RAM_BE(64, 88)
`css_mcu0_EL2_RAM_BE(32, 88)
`css_mcu0_EL2_RAM(64, 39)
/*pragma coverage on*/


`undef css_mcu0_EL2_RAM
`undef css_mcu0_EL2_RAM_BE
`undef css_mcu0_EL2_LOCAL_RAM_TEST_IO


