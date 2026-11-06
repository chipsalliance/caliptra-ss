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

`ifndef CALIPTRA_SS_USB_OCP_DISCONNECT_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_DISCONNECT_SEQUENCE_SV

class caliptra_ss_usb_ocp_disconnect_sequence
    extends caliptra_ss_usb_ocp_post_sync_arbiter_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_disconnect_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_ocp_disconnect_sequence");
        super.new(name);
    endfunction

    protected virtual task ocp_disconnect_issue_dcon_command_and_check_ack(input bit connected);
        bit acknowledged;
        logic [15:0] generation;

        generation = snapshot_generation;
        snapshot_generation++;
        observer_vif.issue_mcu_command_bounded(
            connected ?
                observer_vif.MCU_COMMAND_SET_DCON :
                observer_vif.MCU_COMMAND_CLEAR_DCON,
            generation,
            4'h0,
            ARBITER_HANDSHAKE_TIMEOUT,
            acknowledged);
        if (!acknowledged) begin
            `uvm_fatal("OCP_DISCONNECT",
                $sformatf("DCON command generation %0d was not acknowledged.",
                          generation))
        end
    endtask

    protected virtual task ocp_disconnect_poll_host_state(
        input svt_usb_types::link20sm_state_enum expected_state,
        input string label);
        bit reached;

        reached = 1'b0;
        for (int unsigned poll = 0; poll < 2000; poll++) begin
            if (host_agent_h.shared_status.link_usb_20_state ==
                    expected_state) begin
                reached = 1'b1;
                break;
            end
            #1us;
        end
        if (!reached) begin
            `uvm_fatal("OCP_DISCONNECT",
                $sformatf("%s did not reach host link state %p.",
                          label, expected_state))
        end
    endtask

    protected virtual task ocp_disconnect_poll_and_check_host_not_enabled(input string label);
        bit reached;

        reached = 1'b0;
        for (int unsigned poll = 0; poll < 2000; poll++) begin
            if (host_agent_h.shared_status.link_usb_20_state !=
                    svt_usb_types::ENABLED) begin
                reached = 1'b1;
                break;
            end
            #1us;
        end
        if (!reached) begin
            `uvm_fatal("OCP_DISCONNECT",
                $sformatf("%s did not remove the host link from ENABLED.",
                          label))
        end
        for (int unsigned stable_poll = 0; stable_poll < 20; stable_poll++) begin
            #1us;
            if (host_agent_h.shared_status.link_usb_20_state ==
                    svt_usb_types::ENABLED) begin
                `uvm_fatal("OCP_DISCONNECT",
                    $sformatf("%s returned to ENABLED during the stability window.",
                              label))
            end
        end
    endtask

    protected virtual task ocp_disconnect_do_stop_sof();
        svt_usb_protocol_service_20_sof_off_sequence sof_off;

        sof_off =
            svt_usb_protocol_service_20_sof_off_sequence::type_id::create(
                "ocp_sof_off");
        sof_off.start(p_sequencer.prot_service_sequencer);
    endtask

    protected virtual task ocp_disconnect_configure_host_address_zero();
        usb_cfg.remote_device_cfg[0].device_address = 7'd0;
        host_agent_h.reconfigure(usb_cfg);
        dev_addr_v = 0;
    endtask

    protected virtual task ocp_disconnect_do_reconnect_and_check_access(
        input string label,
        input bit sof_running);
        caliptra_ss_usb_init_sequence init_seq;
        bit [7:0] ignored_response[$];
        caliptra_ss_usb_ocp_xfer_result_e ignored_result;

        init_seq = caliptra_ss_usb_init_sequence::type_id::create(
            {label, "_init"});
        init_seq.post_reset_only = sof_running;
        init_seq.start(p_sequencer, this);
        dev_addr_v = 1;
        ocp_do_discover_and_check_functional_descriptor();
        ocp_arb_do_claimed_read(
            OCP_CMD_PROT_CAP,
            16'(wMaxRdTransferSize),
            ignored_response,
            ignored_result,
            {label, "_PROT_CAP"},
            1'b1);
    endtask

    protected virtual task ocp_disconnect_do_vbus_cycle_and_check_reconnect(input string label);
        svt_usb_physical_service_vbus_off_sequence vbus_off;
        svt_usb_physical_service_vbus_on_sequence vbus_on;

        vbus_off =
            svt_usb_physical_service_vbus_off_sequence::type_id::create(
                {label, "_vbus_off"});
        vbus_on =
            svt_usb_physical_service_vbus_on_sequence::type_id::create(
                {label, "_vbus_on"});
        ocp_disconnect_do_stop_sof();
        vbus_off.start(p_sequencer.usb_20_phys_service_sequencer);
        ocp_disconnect_poll_host_state(svt_usb_types::POWERED_OFF, label);
        ocp_disconnect_issue_dcon_command_and_check_ack(1'b0);
        ocp_disconnect_configure_host_address_zero();
        vbus_on.start(p_sequencer.usb_20_phys_service_sequencer);
        ocp_disconnect_issue_dcon_command_and_check_ack(1'b1);
        ocp_disconnect_do_reconnect_and_check_access(label, 1'b0);
    endtask

    virtual task body();
        bit dcon_only;
        bit [7:0] ignored_response[$];
        caliptra_ss_usb_ocp_xfer_result_e ignored_result;

        dcon_only = 1'b0;
        void'(uvm_config_db#(bit)::get(
            null, get_full_name(), "dcon_only", dcon_only));
        ocp_arb_do_initialize_and_check_transport();
        ocp_arb_do_claimed_read(
            OCP_CMD_PROT_CAP,
            16'(wMaxRdTransferSize),
            ignored_response,
            ignored_result,
            "OCP_DISCONNECT_PRECHECK",
            1'b1);

        if (dcon_only) begin
            bit axi_idle;
            ocp_disconnect_issue_dcon_command_and_check_ack(1'b0);
            ocp_disconnect_poll_and_check_host_not_enabled("DCON clear");
            observer_vif.wait_for_mcu_axi_idle(100us, axi_idle);
            if (!axi_idle) begin
                `uvm_error("OCP_DISCONNECT",
                    "MCU AXI did not become idle after DCON clear.")
            end
            ocp_publish_transfer_count();
            `uvm_info("OCP_DISCONNECT",
                "DCON clear removed the configured USB link after a claimed OCP transfer.",
                UVM_NONE)
            return;
        end

        ocp_disconnect_do_vbus_cycle_and_check_reconnect("OCP_VBUS_RECONNECT");

        begin
            bit axi_idle;
            observer_vif.wait_for_mcu_axi_idle(100us, axi_idle);
            if (!axi_idle) begin
                `uvm_error("OCP_DISCONNECT",
                    "MCU AXI did not become idle after VBUS reconnect.")
            end
        end
        ocp_publish_transfer_count();
        `uvm_info("OCP_DISCONNECT",
            "VBUS-loss recovery completed with post-reconnect OCP access.",
            UVM_NONE)
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_DISCONNECT_SEQUENCE_SV
