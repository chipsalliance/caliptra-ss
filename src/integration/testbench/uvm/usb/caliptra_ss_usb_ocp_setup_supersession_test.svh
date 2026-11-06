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

`ifndef CALIPTRA_SS_USB_OCP_SETUP_SUPERSESSION_TEST_SVH
`define CALIPTRA_SS_USB_OCP_SETUP_SUPERSESSION_TEST_SVH

class caliptra_ss_usb_ocp_setup_supersession_test
    extends caliptra_ss_usb_ocp_arbiter_test_base;

    `uvm_component_utils(caliptra_ss_usb_ocp_setup_supersession_test)

    caliptra_ss_usb_supersession_checker mixed_checker;
    caliptra_ss_usb_supersession_fault_callback fault_callback;
    caliptra_ss_usb_supersession_tx_callback tx_callback;

    function new(string name = "caliptra_ss_usb_ocp_setup_supersession_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        mixed_checker = caliptra_ss_usb_supersession_checker::type_id::create(
            "mixed_checker", this);
        uvm_config_db#(caliptra_ss_usb_supersession_checker)::set(
            null, "*", "usb_supersession_checker", mixed_checker);
        fault_callback = caliptra_ss_usb_supersession_fault_callback::type_id::create(
            "fault_callback");
        fault_callback.sink = mixed_checker;
        tx_callback = caliptra_ss_usb_supersession_tx_callback::type_id::create(
            "tx_callback");
        tx_callback.source = fault_callback;
        uvm_config_db#(caliptra_ss_usb_supersession_fault_callback)::set(
            null, "*", "usb_supersession_fault_callback", fault_callback);
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            caliptra_ss_usb_ocp_setup_supersession_sequence::type_id::get());
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        caliptra_ss_usb_ocp_recovery_env recovery_env;
        super.connect_phase(phase);
        if (!$cast(recovery_env, env))
            `uvm_fatal("SUPERSESSION_PORT", "OCP recovery environment is unavailable")
        mixed_checker.expected_report.link_reporter = env.host_agent.link.reporter;
        if (mixed_checker.expected_report.link_reporter == null)
            `uvm_fatal("SUPERSESSION_EXPECTED", "Actual host-link reporter is unavailable")
        uvm_callbacks#(svt_usb_link_monitor, svt_usb_link_monitor_callback)::add(
            env.host_agent.link_mon, mixed_checker.packet_callback);
        recovery_env.host_transfer_observed_port.connect(
            mixed_checker.protocol_sub.analysis_export);
        uvm_callbacks#(svt_usb_protocol, svt_usb_protocol_callbacks)::add(
            env.host_agent.prot, fault_callback);
        uvm_callbacks#(svt_usb_link, svt_usb_link_callback)::add(
            env.host_agent.link, tx_callback);
    endfunction

    virtual function void final_phase(uvm_phase phase);
        mixed_checker.expected_report.close();
        uvm_callbacks#(svt_usb_link_monitor, svt_usb_link_monitor_callback)::delete(
            env.host_agent.link_mon, mixed_checker.packet_callback);
        uvm_callbacks#(svt_usb_protocol, svt_usb_protocol_callbacks)::delete(
            env.host_agent.prot, fault_callback);
        uvm_callbacks#(svt_usb_link, svt_usb_link_callback)::delete(
            env.host_agent.link, tx_callback);
        super.final_phase(phase);
    endfunction
endclass

`endif
