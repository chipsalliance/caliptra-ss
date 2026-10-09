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

interface caliptra_ss_usb_ocp_collision_if (
    input logic clk,
    input logic rst_ni,
    input logic usb_req,
    input logic usb_ack,
    input logic usb_err,
    input logic usb_write,
    input logic [7:0] usb_cmd,
    input logic [15:0] usb_offset,
    input logic [31:0] usb_wdata,
    input logic [3:0] usb_wstrb,
    input logic ahb_dv,
    input logic ahb_hld,
    input logic ahb_err,
    input logic ahb_write,
    input logic [10:0] ahb_addr,
    input logic [31:0] ahb_wdata,
    input logic [31:0] ahb_rdata,
    input logic cpuif_req,
    input logic [31:0] cpuif_rdata,
    input logic [31:0] recovery_ctrl
);
    import caliptra_ss_usb_ocp_recovery_tb_pkg::*;

    localparam logic [3:0] MCU_START = 4'h8;
    localparam logic [3:0] MCU_STOP = 4'h9;
    localparam int unsigned PROT_READ_EXT_READ = 0;
    localparam int unsigned PROT_READ_EXT_WRITE = 1;
    localparam int unsigned CTRL_WRITE_EXT_READ = 2;
    localparam int unsigned CTRL_WRITE_EXT_WRITE = 3;
    localparam logic [10:0] PROT_CAP_FIRMWARE_WORD_ADDR =
        OCP_ADDR_PROT_CAP[10:0] + 11'd8;

    bit armed = 0;
    bit capture_enabled = 1;
    int unsigned scenario_id;
    logic [10:0] target_addr;
    logic [31:0] prot_cap_word;
    logic [31:0] expected_ctrl;
    logic [31:0] usb_ctrl_word;
    int unsigned blocked_hits;
    int unsigned tail_hits;
    int unsigned deferred_read_hits;
    int unsigned issues;
    int unsigned completions;
    bit in_flight = 0;
    int unsigned request_issues;
    int unsigned request_cycles;
    logic [10:0] held_addr;
    logic held_write;
    logic [31:0] held_wdata;
    bit request_was_blocked;
    event collision_observed;

    wire scenario_match = ahb_addr == target_addr &&
        ahb_write == scenario_id[0] &&
        usb_write == (scenario_id >= CTRL_WRITE_EXT_READ) &&
        usb_cmd == ((scenario_id >= CTRL_WRITE_EXT_READ) ?
                    OCP_CMD_RECOVERY_CTRL : OCP_CMD_PROT_CAP);

    // Occurrence coverage deliberately does not include correctness predicates.
    // A priority defect must fail the checker, not silently erase coverage.
    blocked_collision: cover property (
        @(posedge clk) disable iff (!rst_ni || !armed || !capture_enabled)
        scenario_match && usb_req && ahb_dv && ahb_hld)
    begin
        blocked_hits++;
        -> collision_observed;
    end

    completion_overlap: cover property (
        @(posedge clk) disable iff (!rst_ni || !armed || !capture_enabled)
        scenario_match && usb_ack && ahb_dv && !ahb_hld)
    begin
        tail_hits++;
        -> collision_observed;
    end

    deferred_updated_read: cover property (
        @(posedge clk) disable iff (!rst_ni || !armed || !capture_enabled)
        scenario_id == CTRL_WRITE_EXT_READ && ahb_dv && !ahb_hld &&
        !ahb_write && request_was_blocked && cpuif_rdata == 32'h00000100)
    begin
        deferred_read_hits++;
        -> collision_observed;
    end

    task automatic arm(input int unsigned next_scenario_id,
                       input logic [31:0] capability_word,
                       input logic [31:0] initial_ctrl);
        @(negedge clk);
        scenario_id = next_scenario_id;
        target_addr = (scenario_id >= CTRL_WRITE_EXT_READ) ?
            OCP_ADDR_RECOVERY_CTRL[10:0] : PROT_CAP_FIRMWARE_WORD_ADDR;
        prot_cap_word = capability_word;
        expected_ctrl = initial_ctrl;
        usb_ctrl_word = '0;
        blocked_hits = 0;
        tail_hits = 0;
        deferred_read_hits = 0;
        issues = 0;
        completions = 0;
        in_flight = 0;
        request_was_blocked = 0;
        // Negative validation disables only event capture, never DUT traffic.
        capture_enabled = !$test$plusargs("OCP_COLLISION_SUPPRESS_OBSERVATION");
        armed = 1;
    endtask

    task automatic set_usb_ctrl(input logic [31:0] value);
        @(negedge clk);
        usb_ctrl_word = value;
    endtask

    task automatic finish();
        @(negedge clk);
        if (in_flight || issues == 0 || issues != completions)
            $fatal(1, "OCP_COLLISION: scenario %0d incomplete EXT traffic: issues=%0d completions=%0d pending=%0b",
                   scenario_id, issues, completions, in_flight);
        armed = 0;
    endtask

    always @(posedge clk) begin
        if (armed) begin
            if (!rst_ni)
                $fatal(1, "OCP_COLLISION: reset interrupted an armed scenario");
            if (recovery_ctrl !== expected_ctrl)
                $fatal(1, "OCP_COLLISION: scenario %0d storage=%08h expected=%08h",
                       scenario_id, recovery_ctrl, expected_ctrl);
            if (usb_req && cpuif_req)
                $fatal(1, "OCP_COLLISION: EXT issued while USB owned the register path");
            if (cpuif_req && !ahb_dv)
                $fatal(1, "OCP_COLLISION: CPUif issue without an EXT request");
            if (in_flight && !ahb_dv)
                $fatal(1, "OCP_COLLISION: EXT request disappeared without completion");
            if (ahb_dv && !in_flight) begin
                in_flight = 1;
                held_addr = ahb_addr;
                held_write = ahb_write;
                held_wdata = ahb_wdata;
                request_issues = 0;
                request_cycles = 0;
                request_was_blocked = 0;
            end
            if (in_flight) begin
                request_cycles++;
                if (request_cycles > 512)
                    $fatal(1, "OCP_COLLISION: EXT completion timed out");
                if ({ahb_addr, ahb_write} !== {held_addr, held_write} ||
                    (held_write && ahb_wdata !== held_wdata))
                    $fatal(1, "OCP_COLLISION: held EXT request changed");
                if (ahb_addr != target_addr || ahb_write != scenario_id[0])
                    $fatal(1, "OCP_COLLISION: unexpected EXT address/direction");
                if (usb_req && usb_write && usb_ack && request_issues == 0)
                    request_was_blocked = 1;
                if (cpuif_req) begin
                    request_issues++;
                    issues++;
                    if (request_issues != 1)
                        $fatal(1, "OCP_COLLISION: duplicate EXT CPUif issue");
                    if (ahb_write) begin
                        if (scenario_id == PROT_READ_EXT_WRITE &&
                            ahb_wdata !== prot_cap_word)
                            $fatal(1, "OCP_COLLISION: capability stress write changed runtime capabilities");
                        if (scenario_id == CTRL_WRITE_EXT_WRITE) begin
                            // OCP v1.1 Sec 9.2: CMS=0, image=CMS, no activation.
                            if (ahb_wdata !== 32'h00000100)
                                $fatal(1, "OCP_COLLISION: incorrect firmware RECOVERY_CTRL payload");
                            expected_ctrl = ahb_wdata;
                        end
                    end else if (cpuif_rdata !==
                        ((scenario_id == PROT_READ_EXT_READ) ?
                         prot_cap_word : expected_ctrl)) begin
                        $fatal(1, "OCP_COLLISION: EXT read=%08h expected=%08h",
                               cpuif_rdata,
                               (scenario_id == PROT_READ_EXT_READ) ?
                               prot_cap_word : expected_ctrl);
                    end
                end
                if (!ahb_hld) begin
                    if (ahb_err || request_issues != 1)
                        $fatal(1, "OCP_COLLISION: premature/error EXT completion");
                    if (!ahb_write && ahb_rdata !==
                        ((scenario_id == PROT_READ_EXT_READ) ?
                         prot_cap_word : expected_ctrl))
                        $fatal(1, "OCP_COLLISION: adapter AHB read data mismatch");
                    completions++;
                    in_flight = 0;
                    request_was_blocked = 0;
                end
                if (usb_req && request_issues == 0 && !ahb_hld)
                    $fatal(1, "OCP_COLLISION: unissued EXT request was not held");
            end
            if (usb_req && usb_ack && usb_write &&
                usb_cmd == OCP_CMD_RECOVERY_CTRL) begin
                if (usb_err || usb_offset != 0 || usb_wstrb != 4'h7 ||
                    usb_wdata[23:0] !== usb_ctrl_word[23:0])
                    $fatal(1, "OCP_COLLISION: USB RECOVERY_CTRL write did not commit the requested payload");
                expected_ctrl = {8'h00, usb_ctrl_word[23:0]};
            end
        end
    end
endinterface
