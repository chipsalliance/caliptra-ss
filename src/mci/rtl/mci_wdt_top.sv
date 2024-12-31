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
//
// Description:
//     Intantiate all WDTs and required glue logic 
//

module mci_wdt_top 
    #(
    parameter  WDT_TIMEOUT_PERIOD_NUM_DWORDS = 2,
    localparam WDT_TIMEOUT_PERIOD_W = WDT_TIMEOUT_PERIOD_NUM_DWORDS * 32
    )
    (
    input logic clk,

    // MCI Resets
    input logic rst_b,

    //Timer inputs
    input  logic timer1_en,
    input  logic timer2_en,
    input  logic timer1_restart,
    input  logic timer2_restart,
    input  logic [WDT_TIMEOUT_PERIOD_W-1:0] timer1_timeout_period,
    input  logic [WDT_TIMEOUT_PERIOD_W-1:0] timer2_timeout_period,
    //Interrupts
    input  logic wdt_timer1_timeout_serviced,
    input  logic wdt_timer2_timeout_serviced,
    //WDT STATUS bits 
    output logic t1_timeout_p,
    output logic t2_timeout_p

    );
    
logic t1_timeout;
logic t2_timeout;
logic t1_timeout_f;
logic t2_timeout_f;

//Generate t1 and t2 timeout interrupt pulse
always_ff @(posedge clk or negedge rst_b) begin
    if(!rst_b) begin
        t1_timeout_f <= 'b0;
        t2_timeout_f <= 'b0;
    end
    else begin
        t1_timeout_f <= t1_timeout;
        t2_timeout_f <= t2_timeout;
    end
end

always_comb t1_timeout_p = t1_timeout & ~t1_timeout_f;
always_comb t2_timeout_p = t2_timeout & ~t2_timeout_f;

mci_wdt #(
    .WDT_TIMEOUT_PERIOD_NUM_DWORDS(WDT_TIMEOUT_PERIOD_NUM_DWORDS)
) i_mci_wdt (

    .clk,
    .rst_b,

    .timer1_en,
    .timer2_en,
    .timer1_restart,
    .timer2_restart,
    .timer1_timeout_period,
    .timer2_timeout_period,
    //Interrupts
    .wdt_timer1_timeout_serviced,
    .wdt_timer2_timeout_serviced,
    //WDT STATUS bits
    .t1_timeout,
    .t2_timeout
);


endmodule
