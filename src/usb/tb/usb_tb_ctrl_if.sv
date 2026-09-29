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
// Testbench-owned AXI USER filter policy for the USB wrapper. Both enables
// start known low (bypass) and every allowlist entry starts known zero, so
// tests that never program a policy see deterministic unfiltered traffic.
// The policy signals are synchronous to clk: after time 0 the testbench
// changes them only with nonblocking assignments at a clk rising edge.
// rst_n is observation-only; this interface does not own reset or PHY lock
// sequencing. Kept independent of usb_tb_pkg to avoid a compile cycle.
interface usb_tb_ctrl_if #(
  parameter int unsigned UW = 32,
  parameter int unsigned DEV0_NUM_USERS = 4,
  parameter int unsigned DEV1_NUM_USERS = 4
) (
  input logic clk,
  input logic rst_n
);
  logic dev0_enable_axi_user_filtering;
  logic [UW-1:0] dev0_priv_axi_users [DEV0_NUM_USERS];
  logic dev1_enable_axi_user_filtering;
  logic [UW-1:0] dev1_priv_axi_users [DEV1_NUM_USERS];

  initial begin
    dev0_enable_axi_user_filtering = 1'b0;
    dev1_enable_axi_user_filtering = 1'b0;
    foreach (dev0_priv_axi_users[user_index]) begin
      dev0_priv_axi_users[user_index] = '0;
    end
    foreach (dev1_priv_axi_users[user_index]) begin
      dev1_priv_axi_users[user_index] = '0;
    end
  end
endinterface
