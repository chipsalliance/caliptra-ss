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
module usb_ocp_post_sync_arb_tb;
    timeunit 1ps;
    timeprecision 1ps;
    import uvm_pkg::*;
    import usb_ocp_post_sync_arb_test_pkg::*;

    localparam int unsigned FAST_PERIOD_PS = 2500;
    localparam int unsigned SLOW_PERIOD_PS = 16666;
    caliptra_ss_usb_ocp_rx_drain_unit_if fast_if();
    caliptra_ss_usb_ocp_rx_drain_unit_if slow_if();
    caliptra_ss_usb_ocp_rx_drain_unit #(
        .CLOCK_PERIOD_PS(FAST_PERIOD_PS), .CLOCK_MHZ(400),
        .MIN_CLOCK_PERIOD_PS(SLOW_PERIOD_PS)) fast_unit(fast_if);
    caliptra_ss_usb_ocp_rx_drain_unit #(
        .CLOCK_PERIOD_PS(SLOW_PERIOD_PS), .CLOCK_MHZ(60),
        .MIN_CLOCK_PERIOD_PS(SLOW_PERIOD_PS)) slow_unit(slow_if);

    initial begin
        uvm_config_db#(virtual caliptra_ss_usb_ocp_rx_drain_unit_if)::set(
            null, "uvm_test_top", "fast_vif", fast_if);
        uvm_config_db#(virtual caliptra_ss_usb_ocp_rx_drain_unit_if)::set(
            null, "uvm_test_top", "slow_vif", slow_if);
        run_test("usb_ocp_post_sync_arb_test");
    end
endmodule
