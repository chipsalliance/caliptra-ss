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

`ifndef CALIPTRA_SS_USB_OCP_RECOVERY_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_RECOVERY_SEQUENCE_SV

class caliptra_ss_usb_ocp_recovery_sequence
    extends caliptra_ss_usb_ocp_recovery_base_sequence;

    typedef enum int unsigned {
        RECOVERY_ERROR_UNSUPPORTED_INDIRECT_CTRL,
        RECOVERY_ERROR_PROT_CAP_READ_ONLY,
        RECOVERY_ERROR_FIFO_STATUS_READ_ONLY
    } recovery_error_case_e;

    `uvm_object_utils(caliptra_ss_usb_ocp_recovery_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    covergroup error_recovery_cg with function sample(
        recovery_error_case_e sampled_case);
        option.per_instance = 1;
        cp_error_case: coverpoint sampled_case;
    endgroup

    function new(string name = "caliptra_ss_usb_ocp_recovery_sequence");
        super.new(name);
        error_recovery_cg = new();
    endfunction

    virtual task body();
        bit [15:0] initial_agent_caps;
        bit [7:0]  image_bytes[$];
        bit        recovery_pending_seen;
        recovery_error_case_e selected_error_case;

        ocp_do_initialize_and_check_transport();
        ocp_do_read_and_check_recovery_capabilities(
            "OCPREC_PROT_CAP", initial_agent_caps);
        ocp_do_poll_firmware_ready_status();

        selected_error_case = recovery_error_case_e'(
            $urandom_range(RECOVERY_ERROR_FIFO_STATUS_READ_ONLY,
                           RECOVERY_ERROR_UNSUPPORTED_INDIRECT_CTRL));
        error_recovery_cg.sample(selected_error_case);
        `uvm_info("OCPREC",
            $sformatf({"Selected protocol-error recovery case %s. ",
                       "The seed reproduces this selection."},
                      selected_error_case.name()),
            UVM_NONE)
        case (selected_error_case)
            RECOVERY_ERROR_UNSUPPORTED_INDIRECT_CTRL:
                ocp_do_unsupported_indirect_ctrl_and_check_protocol_error();
            RECOVERY_ERROR_PROT_CAP_READ_ONLY:
                ocp_do_prot_cap_write_and_check_rejection(initial_agent_caps);
            RECOVERY_ERROR_FIFO_STATUS_READ_ONLY:
                ocp_do_fifo_status_write_and_check_rejection();
            default:
                `uvm_fatal("OCPREC", "Unsupported recovery error case.")
        endcase

        ocp_do_recovery_init_xfer(8'h00, 8'h00, "OCPREC_RECOVERY_CTRL");
        ocp_do_fifo_reset_config_xfer(8'h00, 12, "OCPREC_INDIRECT_FIFO_CTRL");
        ocp_do_read_and_check_fifo_ctrl(
            8'h00, 12, "OCPREC_INDIRECT_FIFO_CTRL_RDBK");
        ocp_prepare_default_recovery_image(12, image_bytes);
        ocp_do_single_batch_fifo_image_xfer(image_bytes, "OCPREC_INDIRECT_FIFO_DATA");
        ocp_do_read_and_check_fifo_write_index(12, "OCPREC_INDIRECT_FIFO_STATUS");
        ocp_do_poll_recovery_pending(recovery_pending_seen);

        if (recovery_pending_seen) begin
            ocp_do_recovery_activation_xfer(
                8'h00, 8'h00, "OCPREC_RECOVERY_CTRL_ACTIVATE");
        end

        ocp_hold_for_legacy_completion(recovery_pending_seen);
        ocp_publish_transfer_count();

        `uvm_info("OCPREC", "OCP recovery sequence complete", UVM_NONE)
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_RECOVERY_SEQUENCE_SV
