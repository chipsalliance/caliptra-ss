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
package usb_ocp_post_sync_arb_test_pkg;
    timeunit 1ps;
    timeprecision 1ps;
    import uvm_pkg::*;
    `include "uvm_macros.svh"

    class usb_ocp_post_sync_arb_test extends uvm_test;
        `uvm_component_utils(usb_ocp_post_sync_arb_test)
        virtual caliptra_ss_usb_ocp_rx_drain_unit_if fast_vif, slow_vif;

        function new(string name = "usb_ocp_post_sync_arb_test", uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            if (!uvm_config_db#(virtual caliptra_ss_usb_ocp_rx_drain_unit_if)::get(
                    this, "", "fast_vif", fast_vif) ||
                !uvm_config_db#(virtual caliptra_ss_usb_ocp_rx_drain_unit_if)::get(
                    this, "", "slow_vif", slow_vif))
                `uvm_fatal("OCP_ARB_UNIT", "Missing standalone unit interfaces.")
        endfunction

        task run_phase(uvm_phase phase);
            bit completed;
            phase.raise_objection(this);
            completed = 0;
            fast_vif.request_generation = 16'd1;
            slow_vif.request_generation = 16'd1;
            fast_vif.start = 1;
            slow_vif.start = 1;
            fork : bounded_completion
                begin
                    wait (fast_vif.done === 1'b1 && slow_vif.done === 1'b1 &&
                          fast_vif.completed_generation === 16'd1 &&
                          slow_vif.completed_generation === 16'd1);
                    completed = 1;
                end
                begin
                    #2ms;
                end
            join_any
            disable bounded_completion;
            fast_vif.start = 0;
            slow_vif.start = 0;
            if (!completed)
                `uvm_fatal("OCP_ARB_UNIT", "Missing fresh bounded completion at both clocks.")
            phase.drop_objection(this);
        endtask

        function void check_unit(
                virtual caliptra_ss_usb_ocp_rx_drain_unit_if vif, int unsigned mhz);
            if (vif.errors != 0 || vif.clock_mhz != mhz ||
                vif.running !== 1'b0 || vif.reset_n !== 1'b0 ||
                vif.done !== 1'b1 || vif.completed_generation !== 16'd1 ||
                vif.cases != vif.EXPECTED_CASES ||
                vif.fifo_bound_checks != vif.EXPECTED_FIFO_BOUND_CHECKS ||
                vif.notification_checks != vif.EXPECTED_NOTIFICATION_CHECKS ||
                vif.reset_boundary_checks != vif.EXPECTED_RESET_BOUNDARY_CHECKS ||
                vif.mandatory_bins != 38 || vif.reset_priority_bins != 12 ||
                vif.acceptance_emergency_checks < 2 ||
                vif.reset_setup_high_checks != 72 ||
                vif.dma_immediate_checks != 1 || vif.dma_held_checks != 4)
                `uvm_error("OCP_ARB_UNIT", $sformatf("Incomplete unit checks at %0d MHz.", mhz))
        endfunction

        function void check_phase(uvm_phase phase);
            super.check_phase(phase);
            check_unit(fast_vif, 400);
            check_unit(slow_vif, 60);
        endfunction

        function void report_phase(uvm_phase phase);
            uvm_report_server server;
            super.report_phase(phase);
            server = uvm_report_server::get_server();
            if (server.get_severity_count(UVM_ERROR) != 0 ||
                server.get_severity_count(UVM_FATAL) != 0)
                `uvm_fatal("OCP_ARB_UNIT", "Standalone arbiter checker failures.")
            `uvm_info("OCP_ARB_UNIT",
                "USB_OCP_POST_SYNC_ARB_PASS: 400/60 MHz, all mandatory checks complete.", UVM_NONE)
        endfunction

        function void final_phase(uvm_phase phase);
            uvm_report_server server;
            super.final_phase(phase);
            server = uvm_report_server::get_server();
            if (server.get_severity_count(UVM_ERROR) != 0 ||
                server.get_severity_count(UVM_FATAL) != 0)
                $display("* TESTCASE FAILED");
            else
                $display("* TESTCASE PASSED");
        endfunction
    endclass
endpackage
