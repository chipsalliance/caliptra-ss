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
// Raw UTMI receive injection is a separate PHY-clocked debug path used only
// by malformed-packet tests.
// rst_n is observation-only; this interface does not own reset or PHY lock
// sequencing. Kept independent of usb_tb_pkg to avoid a compile cycle.
interface usb_tb_ctrl_if #(
  parameter int unsigned UW = 32,
  parameter int unsigned COMBO_NUM_USERS = 4,
  parameter int unsigned DEV1_NUM_USERS = 4
) (
  input logic clk,
  input logic rst_n
);
  logic combo_enable_axi_user_filtering;
  logic [UW-1:0] combo_priv_axi_users [COMBO_NUM_USERS];
  logic dev1_enable_axi_user_filtering;
  logic [UW-1:0] dev1_priv_axi_users [DEV1_NUM_USERS];
  logic raw_utmi_inject_enable;
  logic [7:0] raw_utmi_rxdata;
  logic raw_utmi_rxvalid;
  logic raw_utmi_rxactive;
  logic raw_utmi_rxerror;
  logic [7:0] utmi_txdata;
  logic utmi_txvalid;
  logic utmi_txready;
  logic utmi_suspendm;
  logic utmi_xcvrselect;
  logic utmi_termselect;
  logic [1:0] utmi_opmode;
  logic slow_bus_clock;

  initial begin
    combo_enable_axi_user_filtering = 1'b0;
    dev1_enable_axi_user_filtering = 1'b0;
    raw_utmi_inject_enable = 1'b0;
    raw_utmi_rxdata = 8'h00;
    raw_utmi_rxvalid = 1'b0;
    raw_utmi_rxactive = 1'b0;
    raw_utmi_rxerror = 1'b0;
    slow_bus_clock = 1'b0;
    foreach (combo_priv_axi_users[user_index]) begin
      combo_priv_axi_users[user_index] = '0;
    end
    foreach (dev1_priv_axi_users[user_index]) begin
      dev1_priv_axi_users[user_index] = '0;
    end
  end
endinterface
