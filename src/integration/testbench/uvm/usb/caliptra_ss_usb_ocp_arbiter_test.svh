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

`ifndef CALIPTRA_SS_USB_OCP_ARBITER_TEST_SV
`define CALIPTRA_SS_USB_OCP_ARBITER_TEST_SV

class caliptra_ss_usb_ocp_arbiter_test_base
    extends caliptra_ss_usb_basic_utmi_test;

    `uvm_component_utils(caliptra_ss_usb_ocp_arbiter_test_base)

    function new(string name = "caliptra_ss_usb_ocp_arbiter_test_base",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        set_type_override_by_type(
            caliptra_ss_usb_env::get_type(),
            caliptra_ss_usb_ocp_recovery_env::get_type());
        super.build_phase(phase);
    endfunction

    virtual task mcu_halt_monitor_task(uvm_phase phase);
        virtual caliptra_ss_usb_legacy_ep0_observer_if observer_vif;
        logic [15:0] stop_generation;
        bit acknowledged;
        bit idle;

        if (!uvm_config_db#(
                virtual caliptra_ss_usb_legacy_ep0_observer_if)::get(
                    null, "uvm_test_top.env",
                    "usb_legacy_ep0_observer_if", observer_vif)) begin
            `uvm_fatal("OCP_ARB_TEARDOWN", "MCU observer interface not found")
        end
        // DCON commands can follow the last snapshot, and some derived tests
        // use the command service without snapshot collection.
        stop_generation = observer_vif.last_mcu_command_generation + 16'd1;
        observer_vif.issue_mcu_command_bounded(
            observer_vif.MCU_COMMAND_STOP, stop_generation, 4'h0,
            100us, acknowledged);
        if (!acknowledged) begin
            `uvm_fatal("OCP_ARB_TEARDOWN", "MCU STOP acknowledgement timed out")
        end
        observer_vif.wait_for_mcu_axi_idle(100us, idle);
        if (!idle) begin
            `uvm_fatal("OCP_ARB_TEARDOWN", "MCU AXI did not drain after STOP")
        end
        `uvm_info("phase_ready_to_end",
            $sformatf("OCP arbiter MCU stopped at generation %0d; AXI reads/writes drained.",
                      stop_generation), UVM_NONE)
        phase.drop_objection(
            this, "OCP arbiter MCU stopped and AXI drained");
    endtask

endclass

class caliptra_ss_usb_ocp_arb_001_test
    extends caliptra_ss_usb_ocp_arbiter_test_base;

    `uvm_component_utils(caliptra_ss_usb_ocp_arb_001_test)

    function new(string name = "caliptra_ss_usb_ocp_arb_001_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            caliptra_ss_usb_ocp_arb_001_sequence::type_id::get());
    endfunction
endclass

class caliptra_ss_usb_ocp_arb_002_test
    extends caliptra_ss_usb_ocp_arbiter_test_base;

    `uvm_component_utils(caliptra_ss_usb_ocp_arb_002_test)

    function new(string name = "caliptra_ss_usb_ocp_arb_002_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            caliptra_ss_usb_ocp_arb_002_sequence::type_id::get());
    endfunction
endclass

class caliptra_ss_usb_ocp_arb_003_test
    extends caliptra_ss_usb_ocp_arbiter_test_base;

    `uvm_component_utils(caliptra_ss_usb_ocp_arb_003_test)

    function new(string name = "caliptra_ss_usb_ocp_arb_003_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            caliptra_ss_usb_ocp_arb_003_sequence::type_id::get());
    endfunction
endclass

class caliptra_ss_usb_ocp_arb_004_test
    extends caliptra_ss_usb_ocp_arbiter_test_base;

    `uvm_component_utils(caliptra_ss_usb_ocp_arb_004_test)

    function new(string name = "caliptra_ss_usb_ocp_arb_004_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            caliptra_ss_usb_ocp_arb_004_sequence::type_id::get());
    endfunction

endclass

class caliptra_ss_usb_ocp_arb_005_test
    extends caliptra_ss_usb_ocp_arbiter_test_base;

    `uvm_component_utils(caliptra_ss_usb_ocp_arb_005_test)

    function new(string name = "caliptra_ss_usb_ocp_arb_005_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            caliptra_ss_usb_ocp_arb_005_sequence::type_id::get());
    endfunction
endclass

class caliptra_ss_usb_ocp_arb_006_test
    extends caliptra_ss_usb_ocp_arbiter_test_base;

    `uvm_component_utils(caliptra_ss_usb_ocp_arb_006_test)

    svt_err_check_stats reset_abort_routing_chk;

    function new(string name = "caliptra_ss_usb_ocp_arb_006_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            caliptra_ss_usb_ocp_arb_006_sequence::type_id::get());
    endfunction

    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        reset_abort_routing_chk =
            env.host_agent.prot.chk_cov_mgr.find("rx_packet_routed_check");
        if (reset_abort_routing_chk == null) begin
            `uvm_fatal("end_of_elaboration_phase",
                "Protocol chk_cov_mgr could not find rx_packet_routed_check")
        end
        reset_abort_routing_chk.set_default_fail_effect(
            svt_err_check_stats::EXPECTED);
    endfunction

endclass

class caliptra_ss_usb_ocp_arb_007_test
    extends caliptra_ss_usb_ocp_arbiter_test_base;

    `uvm_component_utils(caliptra_ss_usb_ocp_arb_007_test)

    function new(string name = "caliptra_ss_usb_ocp_arb_007_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            caliptra_ss_usb_ocp_arb_007_sequence::type_id::get());
    endfunction
endclass

`endif // CALIPTRA_SS_USB_OCP_ARBITER_TEST_SV
