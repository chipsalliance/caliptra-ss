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

`ifndef CALIPTRA_SS_USB_OCP_SETUP_STALE_NEGATIVE_SEQUENCE_SVH
`define CALIPTRA_SS_USB_OCP_SETUP_STALE_NEGATIVE_SEQUENCE_SVH

// Controlled firmware lifecycle defect, separate from positive supersession
// credit. USB 2.0 5.5.5/9.4.3: correlate each request to its observed bytes.
class caliptra_ss_usb_ocp_setup_stale_negative_sequence
    extends caliptra_ss_usb_ocp_setup_base_sequence;
    `uvm_object_utils(caliptra_ss_usb_ocp_setup_stale_negative_sequence)

    function new(string name = "caliptra_ss_usb_ocp_setup_stale_negative_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_usb_transfer old_req, ocp_req, probe_req, fresh_req;
        ocp_setup_do_initialize_and_check_capabilities();
        old_req = ocp_setup_configure_request(0, "STALE_ORIGINAL");
        ocp_req = ocp_setup_configure_request(1, "STALE_OCP_BYPASS");
        ocp_setup_arm_scenario(4);
        ocp_setup_do_request_and_check_result(old_req, 1, svt_usb_transfer::SETUP_STAGE, "STALE_ORIGINAL");
        ocp_setup_check_mcu_state(STATE_HELD);
        mixed_checker.ocp_supersession_wait_evidence(0, 0, TRANSFER_TIMEOUT);
        fork
            ocp_setup_do_request_and_check_result(ocp_req, 0, svt_usb_transfer::SETUP_STAGE, "STALE_OCP_BYPASS");
            begin
                mixed_checker.ocp_supersession_wait_evidence(1, 0, TRANSFER_TIMEOUT);
                // Publish the obsolete firmware response only after the new
                // OCP SETUP is externally ACKed. No SRAM inspection is used.
                ocp_setup_issue_mcu_command(CMD_STALE);
                ocp_setup_check_mcu_state(STATE_STALE);
            end
        join
        transfers_issued++;
        ocp_setup_check_request(0, old_req, 0, 0, 0);
        ocp_setup_check_request(1, ocp_req, 1, 1, 1);
        mixed_checker.ocp_supersession_check_window(2);
        mixed_checker.ocp_supersession_check_stale_coverage(old_bytes, new_bytes);

        probe_req = ocp_setup_configure_request(0, "STALE_EXPOSURE");
        ocp_setup_arm_scenario(5);
        fork
            ocp_setup_do_request_and_check_result(probe_req, 0, svt_usb_transfer::DATA_STAGE, "STALE_EXPOSURE");
            ocp_setup_check_and_release_legacy(0, 1);
        join
        // Premature clear deliberately exposes the obsolete signature. Its
        // exact on-wire payload, not a publication snapshot, proves exposure.
        ocp_setup_check_request(0, probe_req, 0, 1, 1, 1);
        mixed_checker.ocp_supersession_check_window(1);
        mixed_checker.ocp_supersession_check_stale_coverage(old_bytes, new_bytes);

        fresh_req = ocp_setup_configure_request(0, "FRESH_AFTER_STALE");
        ocp_setup_arm_scenario(6);
        fork
            ocp_setup_do_request_and_check_result(fresh_req, 0, svt_usb_transfer::DATA_STAGE, "FRESH_AFTER_STALE");
            ocp_setup_check_and_release_legacy(0);
        join
        ocp_setup_check_request(0, fresh_req, 0, 1, 1);
        mixed_checker.ocp_supersession_check_window(1);
        mixed_checker.ocp_supersession_check_stale_coverage(old_bytes, new_bytes);
        ocp_setup_publish_transfer_count();
    endtask
endclass
`endif
