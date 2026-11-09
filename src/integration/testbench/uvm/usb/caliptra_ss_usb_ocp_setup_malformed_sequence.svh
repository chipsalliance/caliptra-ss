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

`ifndef CALIPTRA_SS_USB_OCP_SETUP_MALFORMED_SEQUENCE_SVH
`define CALIPTRA_SS_USB_OCP_SETUP_MALFORMED_SEQUENCE_SVH

// USB 2.0 8.5.3: badCRC SETUP receives no handshake. Short4 with validCRC
// is characterization only; neither case imposes internal IRQ/side-effect rules.
class caliptra_ss_usb_ocp_setup_malformed_sequence
    extends caliptra_ss_usb_ocp_setup_base_sequence;
    `uvm_object_utils(caliptra_ss_usb_ocp_setup_malformed_sequence)

    function new(string name = "caliptra_ss_usb_ocp_setup_malformed_sequence");
        super.new(name);
    endfunction

    protected task ocp_malformed_do_injection_and_check_recovery(input bit shorten);
        svt_usb_transfer malformed_req, recovery_req;
        svt_usb_packet active_packets[$];
        int unsigned saved_timeout, saved_error, saved_nak, saved_stall;
        bit retired;
        realtime packet_end;
        string label;
        label = shorten ? "SHORT4_VALIDCRC" : "SETUP8_BADCRC";
        saved_timeout = usb_cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_timeout;
        saved_error = usb_cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_error;
        saved_nak = usb_cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_nak;
        saved_stall = usb_cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_stall;
        usb_cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_timeout = 0;
        usb_cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_error = 0;
        usb_cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_nak = 0;
        usb_cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_stall = 0;
        host_agent_h.reconfigure(usb_cfg);
        malformed_req = ocp_setup_configure_request(0, label);
        scenario_id = shorten ? 7 : 8;
        scenario_generation = command_generation + 1;
        ocp_setup_issue_mcu_command(CMD_ARM, scenario_id);
        ocp_setup_check_mcu_state(STATE_READY);
        mixed_checker.ocp_supersession_configure_characterization(scenario_generation, dev_addr_v);
        fault_callback.ocp_supersession_configure_fault_window(scenario_generation, dev_addr_v,
            mixed_checker.ocp_supersession_get_setup_line(malformed_req), shorten);
        retired = 0;
        fork : bounded_characterization
            begin
                fork
                    begin
                        start_item(malformed_req, -1, p_sequencer.xfer_sequencer);
                        finish_item(malformed_req, -1);
                    end
                    begin
                        wait (fault_callback.fired &&
                              (mixed_checker.char_data0_packets != 0));
                        // The shipped VIP OTG protocol-callback example uses
                        // packet.end_event.wait_on(). This persistent latch is
                        // for the exact injected packet, not a requested length
                        // prediction or a transient protocol notification.
                        fault_callback.actual_packet.end_event.wait_on();
                        packet_end = $realtime;
                        fault_callback.ocp_supersession_configure_tx_capture_completion();
                        mixed_checker.ocp_supersession_check_fault_transmitted(fault_callback.actual_transfer,
                            fault_callback.actual_packet, packet_end);
                        if (!shorten)
                            mixed_checker.expected_report.ocp_supersession_configure_report_window(scenario_generation,
                                fault_callback.actual_transfer, fault_callback.actual_packet,
                                packet_end, TRANSFER_TIMEOUT);
                        // transaction_ended is the end of the transaction loop,
                        // not an attempt. Zero retries and the drop guard remain
                        // active until no bound packet is in flight.
                        wait (fault_callback.setup_ended || fault_callback.transfer_finished);
                        do begin
                            active_packets.delete();
                            fault_callback.actual_transfer.get_started_not_ended_packets(active_packets);
                            if (active_packets.size() != 0) #1ns;
                        end while (active_packets.size() != 0);
                        if (!fault_callback.transfer_finished)
                            fault_callback.actual_transfer.abort(1'b1);
                        wait (fault_callback.transfer_finished);
                    end
                join
                retired = 1;
            end
            #(CHARACTERIZATION_TIMEOUT);
        join_any
        disable bounded_characterization;
        // Never allow an expected-report handler to survive into recovery,
        // retry reconfiguration, firmware commands or the timeout/fatal path.
        mixed_checker.expected_report.ocp_supersession_configure_report_retirement();
        if (!retired)
            `uvm_fatal("SUPERSESSION_MALFORMED", $sformatf(
                "%s did not retire: bindings=%0d injection=%0d setupEnd=%b transferEnd=%b",
                label, fault_callback.bindings, fault_callback.injections,
                fault_callback.setup_ended, fault_callback.transfer_finished))
        mixed_checker.ocp_supersession_check_characterization(fault_callback.bindings,
            fault_callback.injections, fault_callback.tx_bytes,
            fault_callback.tx_sop_seen && fault_callback.tx_eop_seen &&
            fault_callback.tx_capture_closed &&
            (fault_callback.dropped_descriptors == 0));
        `uvm_info("SUPERSESSION_MALFORMED", $sformatf(
            "%s byte tap: items=%0d SOP=%b EOP=%b closed=%b droppedDescriptors=%0d bytes=%p",
            label, fault_callback.tx_items,
            fault_callback.tx_sop_seen, fault_callback.tx_eop_seen,
            fault_callback.tx_capture_closed, fault_callback.dropped_descriptors,
            fault_callback.tx_bytes), UVM_NONE)
        fault_callback.ocp_supersession_configure_fault_retirement();
        usb_cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_timeout = saved_timeout;
        usb_cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_error = saved_error;
        usb_cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_nak = saved_nak;
        usb_cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_stall = saved_stall;
        host_agent_h.reconfigure(usb_cfg);

        recovery_req = ocp_setup_configure_request(0, {label, "_VALID_RECOVERY"});
        ocp_setup_arm_scenario(shorten ? 9 : 10);
        fork
            ocp_setup_do_request_and_check_result(recovery_req, 0, svt_usb_transfer::DATA_STAGE,
                                                 {label, "_VALID_RECOVERY"});
            ocp_setup_check_and_release_legacy(0);
        join
        ocp_setup_check_request(0, recovery_req, 0, 1, 1);
        mixed_checker.ocp_supersession_check_window(1);
        mixed_checker.ocp_supersession_check_recovery_coverage();
    endtask

    virtual task body();
        ocp_setup_do_initialize_and_check_capabilities();
        ocp_malformed_do_injection_and_check_recovery(1);
        ocp_malformed_do_injection_and_check_recovery(0);
        ocp_setup_publish_transfer_count();
    endtask
endclass
`endif
