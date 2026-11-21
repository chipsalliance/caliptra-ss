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
package usb_ocp_post_sync_arb_unit_pkg;
    // Lifecycle is measured from supplied RX beats and independent sink edges,
    // not the arbiter's implementation-state encoding.
    typedef enum int unsigned {
        PH_PENDING, PH_INCOMPLETE, PH_ELIGIBLE, PH_PARTIAL,
        PH_FINAL, PH_TAIL, PH_POSTDONE, PH_IDLE, PH_COUNT
    } lifecycle_t;
    typedef enum int unsigned {
        EV_SETUP, EV_EMERGENCY, EV_BUS, EV_PORT, EV_DISCONNECT, EV_COUNT
    } event_t;
endpackage

interface caliptra_ss_usb_ocp_rx_drain_unit_if;
    timeunit 1ps;
    timeprecision 1ps;
    import uvm_pkg::*;
    import usb_ocp_post_sync_arb_unit_pkg::*;
    `include "uvm_macros.svh"

    localparam int unsigned EXPECTED_CASES = 82;
    localparam int unsigned EXPECTED_FIFO_BOUND_CHECKS = 3;
    localparam int unsigned EXPECTED_NOTIFICATION_CHECKS = 70;
    localparam int unsigned EXPECTED_RESET_BOUNDARY_CHECKS = 110;
    int unsigned clock_mhz;
    logic clk;
    logic reset_n;
    logic start = 1'b0;
    logic [15:0] request_generation = 0;
    logic [15:0] completed_generation = 0;
    logic running = 1'b0;
    logic done = 1'b0;
    int unsigned errors = 0;
    int unsigned cases = 0;
    int unsigned fifo_bound_checks = 0;
    int unsigned notification_checks = 0;
    int unsigned reset_boundary_checks = 0;
    logic out_valid, out_ready, out_last, emergency_abort, reservation;
    logic [31:0] out_data;
    logic physical_fifo_reset;
    logic expected_physical_reset_window;
    logic fifo_batch_abort, ctrl_xfer_abort;
    logic setup_received, forwarded_setup_received;
    lifecycle_t lifecycle_phase;
    int unsigned mandatory_bins = 0;
    int unsigned acceptance_emergency_checks = 0;
    int unsigned reset_priority_bins = 0;
    int unsigned reset_setup_high_checks = 0;
    int unsigned dma_immediate_checks = 0, dma_held_checks = 0;

    covergroup lifecycle_cg with function sample(lifecycle_t phase_id, event_t event_id);
        option.per_instance = 1;
        phase_cp: coverpoint phase_id { bins phases[] = {[PH_PENDING:PH_IDLE]}; }
        event_cp: coverpoint event_id { bins events[] = {[EV_SETUP:EV_DISCONNECT]}; }
        lifecycle_cross: cross phase_cp, event_cp {
            ignore_bins idle_nonreset =
                binsof(phase_cp) intersect {PH_IDLE} &&
                binsof(event_cp) intersect {EV_SETUP, EV_EMERGENCY};
        }
    endgroup
    lifecycle_cg lifecycle_cov = new();

    function automatic void sample_lifecycle(input lifecycle_t phase_id, input event_t event_id);
        lifecycle_cov.sample(phase_id, event_id);
    endfunction

    // Public decoder handshakes cannot publish another word on an emergency
    // purge edge. Ordinary wire supersession is not a physical FIFO reset.
    emergency_no_push: assert property (
        @(posedge clk) disable iff (!reset_n || !running)
        emergency_abort |-> out_valid === 1'b0)
    else begin
        errors++;
        `uvm_error("OCP_RX_DRAIN_UNIT", "Publication on emergency purge edge.")
    end
    no_destructive_reset: assert property (
        @(posedge clk) disable iff (!reset_n || !running)
        expected_physical_reset_window === 1'b1 || physical_fifo_reset === 1'b0)
    else begin
        errors++;
        `uvm_error("OCP_RX_DRAIN_UNIT", "Ordinary event caused physical FIFO reset.")
    end
    unconditional_physical_reset: assert property (
        @(posedge clk) disable iff (!reset_n || !running)
        physical_fifo_reset === expected_physical_reset_window)
    else begin
        errors++;
        `uvm_error("OCP_RX_DRAIN_UNIT", "Missing or spurious physical FIFO reset.")
    end
    reset_without_diagnosis: assert property (
        @(posedge clk) disable iff (!reset_n || !running)
        expected_physical_reset_window |-> fifo_batch_abort === 1'b0)
    else begin
        errors++;
        `uvm_error("OCP_RX_DRAIN_UNIT", "Physical reset alone diagnosed a batch abort.")
    end
    raw_setup_notification: assert property (
        @(posedge clk) disable iff (!reset_n || !running)
        forwarded_setup_received === setup_received)
    else begin
        errors++;
        `uvm_error("OCP_RX_DRAIN_UNIT", "SETUP notification was qualified or delayed.")
    end
    supported_sink_ready: assert property (
        @(posedge clk) disable iff (!reset_n || !running)
        out_valid |-> out_ready === 1'b1)
    else begin
        errors++;
        `uvm_error("OCP_RX_DRAIN_UNIT", "Integrated-profile sink stalled a drain.")
    end
endinterface
