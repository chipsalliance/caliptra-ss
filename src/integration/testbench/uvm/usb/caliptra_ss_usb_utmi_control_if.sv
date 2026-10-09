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

// Supplies bounded raw receive-packet injection at the subsystem UTMI boundary.
interface caliptra_ss_usb_utmi_control_if (
    input logic utmi_clk
);
    logic inject_enable;
    logic [7:0] rxdata;
    logic rxvalid;
    logic rxactive;
    logic rxerror;

    initial begin
        inject_enable = 1'b0;
        rxdata = 8'h00;
        rxvalid = 1'b0;
        rxactive = 1'b0;
        rxerror = 1'b0;
    end

    // Inject SOF frame zero: PID=A5, frame=0, complemented USB CRC5=0x02.
    task inject_sof_frame_zero();
        @(negedge utmi_clk);
        inject_enable <= 1'b1;
        rxactive <= 1'b1;
        rxvalid <= 1'b1;
        rxerror <= 1'b0;
        rxdata <= 8'ha5;
        @(negedge utmi_clk);
        rxdata <= 8'h00;
        @(negedge utmi_clk);
        rxdata <= 8'h10;
        @(negedge utmi_clk);
        rxvalid <= 1'b0;
        rxactive <= 1'b0;
        rxdata <= 8'h00;
        @(negedge utmi_clk);
        inject_enable <= 1'b0;
    endtask

endinterface
