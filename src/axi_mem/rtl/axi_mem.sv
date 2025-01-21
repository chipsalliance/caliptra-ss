// SPDX-License-Identifier: Apache-2.0
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


module axi_mem #(
    parameter AW = 32,
    parameter DW = 64,
              BC = DW/8,       // Byte Count
              BW = $clog2(BC), // Byte count Width
    parameter UW = 32,         // User Width
    parameter IW = 1,          // ID Width
              ID_NUM = 1 << IW, // Don't override

    parameter EX_EN = 0    // Enable exclusive access tracking w/ AxLOCK
)
(
    input clk,
    input rst_n,

    // AXI INF
    axi_if.w_sub s_axi_w_if,
    axi_if.r_sub s_axi_r_if,

    //COMPONENT INF
    axi_mem_if.request s_mem_req_if
);

//COMPONENT INF
logic          dv;
logic [AW-1:0] addr; // Byte address
logic          write;
logic [DW-1:0] wdata; // Requires: Component dwidth == AXI dwidth
logic [DW-1:0] rdata; // Requires: Component dwidth == AXI dwidth
logic          hold;
logic          rd_error;
logic          wr_error;


axi_sub #(
    .AW   (AW   ),
    .DW   (DW   ),
    .UW   (UW   ),
    .IW   (IW   ),
    .EX_EN(EX_EN),
    .C_LAT(1    )
) i_axi_sub (
    .clk  (clk     ),
    .rst_n(rst_n   ),

    // AXI INF
    .s_axi_w_if(s_axi_w_if),
    .s_axi_r_if(s_axi_r_if),

    //COMPONENT INF
    .dv      (dv      ),
    .addr    (addr    ), // Byte address
    .write   (write   ),
    .user    (        ),
    .id      (        ),
    .wdata   (wdata   ),
    .wstrb   (        ),
    .rdata   (rdata   ),
    .last    (        ),
    .size    (        ),
    .hld     (hold    ),
    .rd_err  (rd_error),
    .wr_err  (wr_error)
);

assign hold = 1'b0;
assign rd_error = 1'b0;
assign wr_error = 1'b0;

assign s_mem_req_if.req.cs   = dv;
assign s_mem_req_if.req.we   = write;
assign s_mem_req_if.req.addr = addr[AW-1:BW];
assign s_mem_req_if.req.wdata.data = wdata;
assign rdata = s_mem_req_if.resp.rdata.data;

endmodule