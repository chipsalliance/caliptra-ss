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

`ifndef CALIPTRA_SS_USB_OCP_SETUP_SUPERSESSION_SEQUENCE_SVH
`define CALIPTRA_SS_USB_OCP_SETUP_SUPERSESSION_SEQUENCE_SVH

// USB 2.0 5.5.5: original owner x DATA/STATUS pending. Host abort only
// retires VIP bookkeeping; the next real SETUP must supersede device work.
class caliptra_ss_usb_ocp_setup_supersession_sequence
    extends caliptra_ss_usb_ocp_setup_base_sequence;
    `uvm_object_utils(caliptra_ss_usb_ocp_setup_supersession_sequence)

    function new(string name = "caliptra_ss_usb_ocp_setup_supersession_sequence");
        super.new(name);
    endfunction

    protected task run_scenario(input logic [3:0] id, input bit original_ocp,
        input svt_usb_transfer::xfer_stage_enum completed_stage, input string label);
        svt_usb_transfer original_req, replacement_req;
        original_req = build_request(original_ocp, {label, "_original"});
        replacement_req = build_request(!original_ocp, {label, "_replacement"});
        arm_scenario(id);
        fork
            execute_request(original_req, 1, completed_stage, {label, "_original"});
            begin
                if (!original_ocp && (completed_stage == svt_usb_transfer::DATA_STAGE))
                    release_legacy(0);
            end
        join
        mixed_checker.wait_evidence(0, 0, TRANSFER_TIMEOUT);
        if (!original_ocp && (completed_stage == svt_usb_transfer::SETUP_STAGE))
            wait_state(STATE_HELD);
        if (original_ocp) transfers_issued++;
        fork
            execute_request(replacement_req, 0, completed_stage, {label, "_replacement"});
            begin
                if (original_ocp) release_legacy(1);
            end
        join
        if (!original_ocp) transfers_issued++;
        check_request(0, original_req, original_ocp, 0,
                      completed_stage == svt_usb_transfer::DATA_STAGE);
        check_request(1, replacement_req, !original_ocp, 1, 1);
        mixed_checker.end_window(2);
        mixed_checker.credit_positive();
    endtask

    virtual task body();
        // Resolve only the checker; synthetic fixtures need no USB discovery.
        if (!uvm_config_db#(caliptra_ss_usb_supersession_checker)::get(
            null, "", "usb_supersession_checker", mixed_checker))
            `uvm_fatal("SETUP_SUPERSESSION", "Boundary scoreboard not configured")
        mixed_checker.negative_selftest();
        prepare();
        run_scenario(0, 0, svt_usb_transfer::SETUP_STAGE, "L_TO_O_DATA_PENDING");
        run_scenario(1, 1, svt_usb_transfer::SETUP_STAGE, "O_TO_L_DATA_PENDING");
        run_scenario(2, 0, svt_usb_transfer::DATA_STAGE, "L_TO_O_STATUS_PENDING");
        run_scenario(3, 1, svt_usb_transfer::DATA_STAGE, "O_TO_L_STATUS_PENDING");
        finish_stimulus();
    endtask
endclass
`endif
