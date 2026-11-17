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

`ifndef CALIPTRA_SS_USB_OCP_BASE_TEST_SV
`define CALIPTRA_SS_USB_OCP_BASE_TEST_SV

class caliptra_ss_usb_ocp_base_test
    extends caliptra_ss_usb_basic_utmi_test;

    `uvm_component_utils(caliptra_ss_usb_ocp_base_test)

    function new(string name = "caliptra_ss_usb_ocp_base_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task mcu_halt_monitor_task(uvm_phase phase);
        virtual caliptra_ss_usb_legacy_ep0_observer_if observer_vif;
        logic [15:0] stop_generation;
        bit acknowledged;
        bit idle;
        bit halted;

        if (!uvm_config_db#(
                virtual caliptra_ss_usb_legacy_ep0_observer_if)::get(
                    null, "uvm_test_top.env",
                    "usb_legacy_ep0_observer_if", observer_vif)) begin
            `uvm_fatal("OCP_TEARDOWN", "MCU observer interface not found")
        end
        // Commands can follow the last snapshot, and some tests use the
        // command service without snapshot collection.
        stop_generation = observer_vif.last_mcu_command_generation + 16'd1;
        observer_vif.issue_mcu_command_bounded(
            observer_vif.MCU_COMMAND_STOP, stop_generation, 4'h0,
            100us, acknowledged);
        if (!acknowledged) begin
            `uvm_fatal("OCP_TEARDOWN", "MCU STOP acknowledgement timed out")
        end
        // The STOP acknowledgement precedes the firmware's halt instruction.
        // An LSU-idle sample alone can end simulation while IFU still runs.
        halted = 1'b0;
        fork : wait_for_stop_halt
            begin
                wait (bfm_if.mcu_halt_status === 1'b1);
                halted = 1'b1;
            end
            begin
                #100us;
            end
        join_any
        disable wait_for_stop_halt;
        if (!halted) begin
            `uvm_fatal("OCP_TEARDOWN", "MCU did not halt after STOP acknowledgement")
        end
        observer_vif.wait_for_mcu_axi_idle(100us, idle);
        if (!idle) begin
            `uvm_fatal("OCP_TEARDOWN", "MCU AXI did not drain after STOP")
        end
        `uvm_info("phase_ready_to_end",
            $sformatf("OCP MCU stopped at generation %0d; AXI reads/writes drained.",
                      stop_generation), UVM_NONE)
        phase.drop_objection(
            this, "OCP MCU stopped and AXI drained");
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_BASE_TEST_SV
