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

`ifndef CALIPTRA_SS_USB_OCP_PROTOCOL_STALL_MATRIX_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_PROTOCOL_STALL_MATRIX_SEQUENCE_SV

class caliptra_ss_usb_ocp_protocol_stall_matrix_sequence
    extends caliptra_ss_usb_ocp_stall_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_protocol_stall_matrix_sequence)

    typedef struct {
        bit dir_in;
        ocp_cmd_t command;
        int unsigned length;
        ocp_protocol_error_e code;
        bit data_stage;
        string label;
    } negative_case_t;

    function new(string name = "caliptra_ss_usb_ocp_protocol_stall_matrix_sequence");
        super.new(name);
    endfunction

    protected task check_first_error_wins();
        bit [7:0] payload[$];
        payload = '{8'h00};
        // First-error-wins is a Caliptra local contract, not OCP Section 9.1.
        issue_stall(1'b0, RESERVED_COMMAND, payload.size(), payload,
            OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND, "LOCAL_FIRST_A");
        issue_stall(1'b0, OCP_CMD_RECOVERY_CTRL, payload.size(), payload,
            OCP_PROTOCOL_ERROR_LENGTH, "LOCAL_SECOND_B");
        read_status_and_check("LOCAL_FIRST_CODE");
        read_status_and_check("LOCAL_CLEAR_NO_DEFERRED_CODE");
        mark_check("local first-code retention; second request still stalled");
    endtask

    virtual task body();
        negative_case_t cases[$];
        bit [7:0] payload[$];
        initialize_stall_transport();

        // OCP Recovery v1.1 Sections 9.1/9.2 define these classes and lengths.
        cases.push_back('{0, RESERVED_COMMAND, 1,
            OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND, 0, "RESERVED_COMMAND"});
        cases.push_back('{0, OCP_CMD_PROT_CAP, 1,
            OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND, 0, "HOST_RO_WRITE"});
        cases.push_back('{0, OCP_CMD_RECOVERY_CTRL, OCP_SPEC_LEN_RECOVERY_CTRL,
            OCP_PROTOCOL_ERROR_UNSUPPORTED_PARAMETER, 1, "RESERVED_IMAGE_SELECTION"});
        cases.push_back('{0, OCP_CMD_RECOVERY_CTRL, 0,
            OCP_PROTOCOL_ERROR_LENGTH, 0, "RC_ZERO"});
        cases.push_back('{0, OCP_CMD_RECOVERY_CTRL, OCP_SPEC_LEN_RECOVERY_CTRL - 1,
            OCP_PROTOCOL_ERROR_LENGTH, 0, "RC_SHORT"});
        cases.push_back('{0, OCP_CMD_RECOVERY_CTRL, OCP_SPEC_LEN_RECOVERY_CTRL + 1,
            OCP_PROTOCOL_ERROR_LENGTH, 0, "RC_LONG"});
        // Wrong read wLength -> 0xFF is a local classification of the
        // OCP Section 8.5.1 violation; Section 9.1 does not assign that code.
        cases.push_back('{1, OCP_CMD_DEVICE_STATUS, wMaxRdTransferSize - 1,
            OCP_PROTOCOL_ERROR_GENERAL, 0, "LOCAL_READ_LENGTH"});
        if (agent_capabilities[OCP_CAP_INDIRECT_FIFO]) begin
            cases.push_back('{0, OCP_CMD_INDIRECT_FIFO_CTRL, 0,
                OCP_PROTOCOL_ERROR_LENGTH, 0, "FIFO_CTRL_ZERO"});
            cases.push_back('{0, OCP_CMD_INDIRECT_FIFO_CTRL,
                OCP_SPEC_LEN_INDIRECT_FIFO_CTRL - 1,
                OCP_PROTOCOL_ERROR_LENGTH, 0, "FIFO_CTRL_SHORT"});
            cases.push_back('{0, OCP_CMD_INDIRECT_FIFO_CTRL,
                OCP_SPEC_LEN_INDIRECT_FIFO_CTRL + 1,
                OCP_PROTOCOL_ERROR_LENGTH, 0, "FIFO_CTRL_LONG"});
            prepare_modeled_fifo((wMaxWrTransferSize + 3) / 4, "FIFO_SETUP");
            cases.push_back('{0, OCP_CMD_INDIRECT_FIFO_DATA, 0,
                OCP_PROTOCOL_ERROR_LENGTH, 0, "FIFO_DATA_ZERO"});
            if (wMaxWrTransferSize < 16'hFFFF)
                cases.push_back('{0, OCP_CMD_INDIRECT_FIFO_DATA, wMaxWrTransferSize + 1,
                    OCP_PROTOCOL_ERROR_LENGTH, 0, "FIFO_DATA_OVER_USB_LIMIT"});
        end
        if (agent_capabilities[OCP_CAP_VENDOR]) begin
            // OCP Section 9.2 leaves VENDOR length implementation-defined.
            // The local contract accepts exactly one byte.
            cases.push_back('{0, OCP_CMD_VENDOR, 0,
                OCP_PROTOCOL_ERROR_LENGTH, 0, "LOCAL_VENDOR_ZERO"});
            cases.push_back('{0, OCP_CMD_VENDOR, 2,
                OCP_PROTOCOL_ERROR_LENGTH, 0, "LOCAL_VENDOR_TWO_BYTES"});
            if (wMaxWrTransferSize < 16'hFFFF)
                cases.push_back('{0, OCP_CMD_VENDOR, wMaxWrTransferSize + 1,
                    OCP_PROTOCOL_ERROR_LENGTH, 0, "LOCAL_VENDOR_OVER_USB_LIMIT"});
        end else begin
            `uvm_info("OCP_STALL",
                "VENDOR length cases not applicable: command not advertised.",
                UVM_NONE)
        end
        foreach (cases[i]) begin
            payload.delete();
            if (!cases[i].dir_in)
                repeat (cases[i].length) payload.push_back(8'h00);
            if (cases[i].data_stage)
                payload[OCP_OFF_RC_IMG_SEL] = RESERVED_IMAGE_SELECTION;
            check_rejected_request(cases[i].dir_in, cases[i].command,
                16'(cases[i].length), payload, cases[i].code,
                cases[i].label, cases[i].data_stage);
        end
        // An internally consistent one-byte transfer carries a format
        // exception advertising the spec-required three bytes on the bus.
        // The mirrored SETUP check independently proves that wire length.
        inject_short_data = 1'b1;
        payload = '{8'h00};
        check_rejected_request(0, OCP_CMD_RECOVERY_CTRL, payload.size(),
            payload, OCP_PROTOCOL_ERROR_LENGTH, "DELIVERED_DATA_SHORT", 1'b1);
        inject_short_data = 1'b0;
        if (agent_capabilities[OCP_CAP_INDIRECT_FIFO]) begin
            prepare_modeled_fifo(1, "FIFO_SMALL_IMAGE");
            payload = '{8'h00, 8'h01, 8'h02, 8'h03, 8'h04};
            check_rejected_request(0, OCP_CMD_INDIRECT_FIFO_DATA,
                payload.size(), payload, OCP_PROTOCOL_ERROR_LENGTH,
                "FIFO_DATA_OVER_IMAGE_REMAINING");
        end
        check_first_error_wins();
        run_unclaimed_configuration_descriptor("STANDARD_BYPASS");
        read_status_and_check("STANDARD_BYPASS_STATUS");
        // USB link CRC is not an OCP checksum. No USB OCP checksum field
        // is defined; code 0x04 is not applicable (OCP Sections 8.5/9.2).
        mark_check("OCP checksum code 0x04 not applicable to USB encapsulation");
        finish_stall_test("PROTOCOL_MATRIX");
    endtask
endclass

`endif
