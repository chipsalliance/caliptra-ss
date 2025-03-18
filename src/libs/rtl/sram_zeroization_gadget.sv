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

// SRAM Zeroization Gadget
// Operation: 
// -Specify start and end dword address 
// -Start pulse triggers zeroization between start and end
// -In progress is asserted while zeroization is running
// -Done is pulsed once zeroization is complete

module sram_zeroization_gadget #(
        parameter SRAM_DEPTH = 512,
        parameter SRAM_DATA_WIDTH = 32,
        localparam SRAM_ADDR_WIDTH = $clog2(SRAM_DEPTH)
    ) (
// Inputs
        input logic clk,
        input logic rst_b,
        input logic sram_start_zeroing,
        input logic [SRAM_ADDR_WIDTH-1:0] sram_zero_start_addr,
        input logic [SRAM_ADDR_WIDTH-1:0] sram_zero_end_addr,
        input logic sram_we_in,
        input logic sram_cs_in,
        input logic [SRAM_DATA_WIDTH-1:0] sram_wr_data_in,
        input logic [SRAM_ADDR_WIDTH-1:0] sram_wr_addr_in,        

// Outputs
        output logic sram_zero_done,
        output logic sram_zero_in_progress,
        output logic sram_we_out, 
        output logic sram_cs_out,
        output logic [SRAM_DATA_WIDTH-1:0] sram_wr_data_out,
        output logic [SRAM_ADDR_WIDTH-1:0] sram_wr_addr_out
    );

    logic sram_zero_addr_at_end;
    logic [SRAM_ADDR_WIDTH-1:0] next_sram_zero_wr_addr;
    logic [SRAM_ADDR_WIDTH-1:0] sram_zero_wr_addr;

    // SRAM Zeroing State Tracking
    // Done : pulse indication that zeroization has completed
    always_ff @(posedge clk or negedge rst_b) begin
        if (!rst_b) begin
            sram_zero_done <= 1'b0;
        end else if (sram_zero_done || sram_start_zeroing) begin
            sram_zero_done <= 1'b0;
        end else if (sram_zero_in_progress && sram_zero_addr_at_end) begin
            sram_zero_done <= 1'b1;
        end
    end

    // In progress : current zeroization status asserted during full duration
    always_ff @(posedge clk or negedge rst_b) begin
        if (!rst_b) begin
            sram_zero_in_progress <= 1'b0;
        end else if (sram_start_zeroing) begin
            sram_zero_in_progress <= 1'b1;
        end else if (sram_zero_in_progress && sram_zero_addr_at_end) begin
            sram_zero_in_progress <= 1'b0;
        end
    end

    // SRAM Zeroing Write address computation
    always_ff @(posedge clk or negedge rst_b) begin
        if (!rst_b) begin
            sram_zero_wr_addr <= '0;
        end else begin
            sram_zero_wr_addr <= next_sram_zero_wr_addr;
        end
    end

    always_comb begin
        next_sram_zero_wr_addr = sram_zero_in_progress ? (sram_zero_addr_at_end ? sram_zero_start_addr : sram_zero_wr_addr + 1) : sram_zero_start_addr;
    end
    
    // Zeroization wr addr has reached end address
    // Include safety check that if write gets past max SRAM size
    always_comb sram_zero_addr_at_end = (sram_zero_wr_addr == sram_zero_end_addr) || (sram_zero_wr_addr >= SRAM_DEPTH-1);

    always_comb begin
        sram_wr_data_out = (sram_zero_in_progress) ? {SRAM_DATA_WIDTH{1'b0}} : sram_wr_data_in;
        sram_wr_addr_out = '0;
        sram_wr_addr_out = (sram_zero_in_progress) ? sram_zero_wr_addr : sram_wr_addr_in;
        sram_we_out   = sram_zero_in_progress || sram_we_in;
        sram_cs_out   = sram_zero_in_progress || sram_cs_in;
    end
endmodule : sram_zeroization_gadget
