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
// One testbench-owned AXI USER filter policy (enable plus allowlist) for a
// USB wrapper filter input group; usb_top_tb instantiates one per policy.
// The enable starts known low (bypass) and every allowlist entry starts known
// zero, so tests that never program a policy see deterministic unfiltered
// traffic. After time 0 only usb_axi_user_filter_driver changes the policy,
// through drv_cb, so updates land at a clk rising edge. rst_n is
// observation-only; this interface does not own reset or PHY lock
// sequencing. Kept independent of any package to avoid a compile cycle.
interface usb_axi_user_filter_if #(
  parameter int unsigned UW = 32,
  parameter int unsigned NUM_USERS = 2
) (
  input logic clk,
  input logic rst_n
);
  logic enable_axi_user_filtering;
  logic [UW-1:0] priv_axi_users [NUM_USERS];

  // Zero output skew: drives update in the Re-NBA region of the edge, so the
  // DUT's flops at that edge still sample the previous policy. Signals are
  // inout so the driver reads back through the same clocking event it drives on.
  clocking drv_cb @(posedge clk);
    default input #1step output #0;
    inout enable_axi_user_filtering;
    inout priv_axi_users;
  endclocking

  // Samples the settled pre-edge policy and reset seen by the DUT.
  clocking mon_cb @(posedge clk);
    default input #1step;
    input enable_axi_user_filtering;
    input priv_axi_users;
    input rst_n;
  endclocking

  initial begin
    enable_axi_user_filtering = 1'b0;
    foreach (priv_axi_users[user_index]) begin
      priv_axi_users[user_index] = '0;
    end
  end
endinterface
