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

// Exercise evidence only. No virtual interface is published and no signal
// here may drive stimulus, expected data, or the functional completion gate.
interface usb_ocp_cov_if #(parameter int HUB_ADDR_WIDTH = 8) (
  input logic clk,
  input logic rst_n,
  input logic hub_select,
  input logic [1:0] hub_transfer,
  input logic hub_write,
  input logic [HUB_ADDR_WIDTH-1:0] hub_address,
  input logic hub_ready_in,
  input logic hub_ready_out,
  input logic [31:0] hub_data,
  input logic ocp_request,
  input logic fifo_push,
  input logic fifo_pop,
  input logic [7:0] activate
);
  logic enabled;
  logic hub_control_pending;
  initial enabled = $test$plusargs("usb_ocp_cov");
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) hub_control_pending <= 0;
    else if (hub_ready_in)
      // Hub CONTROL is byte offset 0x30; this AHB port has word addresses.
      hub_control_pending <= hub_select && hub_transfer[1] && hub_write &&
                             hub_address == HUB_ADDR_WIDTH'('h0c);
  end

  `ifdef FCOV
  ocp_cov_hub_enable: cover property (@(posedge clk) disable iff (!rst_n || !enabled)
    hub_control_pending && hub_ready_out && hub_data[0] && !hub_data[16]);
  ocp_cov_hub_connect: cover property (@(posedge clk) disable iff (!rst_n || !enabled)
    hub_control_pending && hub_ready_out && hub_data[0] && hub_data[16]);
  ocp_cov_request: cover property (@(posedge clk) disable iff (!rst_n || !enabled)
    ocp_request);
  ocp_cov_fifo_push: cover property (@(posedge clk) disable iff (!rst_n || !enabled)
    fifo_push);
  ocp_cov_fifo_pop: cover property (@(posedge clk) disable iff (!rst_n || !enabled)
    fifo_pop);
  ocp_cov_activate: cover property (@(posedge clk) disable iff (!rst_n || !enabled)
    activate == 8'h0f);
  ocp_cov_activate_clear: cover property (@(posedge clk) disable iff (!rst_n || !enabled)
    (activate == 8'h0f) ##1 (activate == 0));
  `endif
endinterface
