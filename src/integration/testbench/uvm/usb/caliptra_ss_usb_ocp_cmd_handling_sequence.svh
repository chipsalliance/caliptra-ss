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

`ifndef CALIPTRA_SS_USB_OCP_CMD_HANDLING_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_CMD_HANDLING_SEQUENCE_SV

class caliptra_ss_usb_ocp_cmd_handling_sequence
    extends caliptra_ss_usb_ocp_recovery_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_cmd_handling_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    localparam bit [7:0] VENDOR_DEFAULT_DATA = 8'h5A;
    localparam bit [7:0] IDENTIFICATION_ENABLE_TOKEN = 8'hA3;
    localparam bit [7:0] IDENTIFICATION_DISABLE_TOKEN = 8'hA4;
    localparam bit [7:0] VENDOR_DISABLE_TOKEN = 8'hA5;
    localparam bit [OCP_SPEC_MIN_LEN_DEVICE_ID*8-1:0]
        EXPECTED_DEVICE_ID =
            192'h0000000000001F1E1D1C1B1A191817161514131211100002;

    protected int unsigned checks_executed[string];

    function new(string name = "caliptra_ss_usb_ocp_cmd_handling_sequence");
        super.new(name);
    endfunction

    protected virtual function void mark_check(
        input string test_id,
        input string detail);

        if (!checks_executed.exists(test_id)) begin
            checks_executed[test_id] = 0;
        end
        checks_executed[test_id]++;
        `uvm_info("OCP_CMD_CHECK",
            $sformatf("%s CHECK_EXECUTED %s", test_id, detail),
            UVM_NONE)
    endfunction

    protected virtual function void check_fixed_length(
        ref bit [7:0] response[$],
        input int expected_length,
        input string label);

        if (response.size() != expected_length) begin
            `uvm_error("OCP_CMD",
                $sformatf("%s response length=%0d, expected %0d.",
                          label, response.size(), expected_length))
        end
    endfunction

    protected virtual task check_heartbeat_behavior(
        input bit [7:0] heartbeat_period);

        bit [7:0] first_status[$];
        bit [7:0] second_status[$];
        bit [15:0] first_heartbeat;
        bit [15:0] second_heartbeat;
        time heartbeat_wait;

        device_status_read_and_check(
            first_status, "OCP_CMD_011_DEVICE_STATUS_FIRST");
        if ((heartbeat_period != 0) && (heartbeat_period <= 12)) begin
            heartbeat_wait = (64'd1 << heartbeat_period) * 1us;
            #(heartbeat_wait + 1us);
        end
        device_status_read_and_check(
            second_status, "OCP_CMD_011_DEVICE_STATUS_SECOND");
        if ((first_status.size() < OCP_SPEC_MIN_LEN_DEVICE_STATUS) ||
            (second_status.size() < OCP_SPEC_MIN_LEN_DEVICE_STATUS)) begin
            return;
        end

        first_heartbeat =
            get_le16(first_status, OCP_OFF_DS_HEARTBEAT_LO);
        second_heartbeat =
            get_le16(second_status, OCP_OFF_DS_HEARTBEAT_LO);

        if ((heartbeat_period == 0) &&
            (first_heartbeat != second_heartbeat)) begin
            `uvm_error("OCP_CMD",
                $sformatf("PROT_CAP reports heartbeat unsupported, but DEVICE_STATUS heartbeat changed from %0d to %0d.",
                          first_heartbeat, second_heartbeat))
        end
        if ((heartbeat_period != 0) && (heartbeat_period <= 12) &&
            (first_heartbeat == second_heartbeat)) begin
            `uvm_error("OCP_CMD",
                $sformatf("Heartbeat period is 2^%0d us, but DEVICE_STATUS heartbeat remained %0d after one advertised period.",
                          heartbeat_period, first_heartbeat))
        end
        if (heartbeat_period > 12) begin
            `uvm_warning("OCP_CMD",
                $sformatf("Heartbeat period exponent %0d exceeds the bounded directed-test observation window; field legality was checked but increment timing is deferred to a long-running flow test.",
                          heartbeat_period))
        end
        mark_check("OCP_CMD_011",
            $sformatf("heartbeat_period=%0d first=%0d second=%0d vendor-length bounds checked",
                      heartbeat_period, first_heartbeat, second_heartbeat));
    endtask

    protected virtual task check_optional_hw_status(
        input bit [15:0] agent_caps);

        bit [7:0] empty_payload[$];
        if (agent_caps[OCP_CAP_HW_STATUS]) begin
            hw_status_read_and_check();
            mark_check("OCP_CMD_007",
                "advertised HW_STATUS accepted and format checked");
        end else begin
            empty_payload.delete();
            ocp_expect_protocol_error(
                1'b1, OCP_CMD_HW_STATUS, empty_payload,
                OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND,
                "OCP_CMD_007_HW_STATUS_UNADVERTISED", 1'b1);
            mark_check("OCP_CMD_007",
                "unadvertised HW_STATUS reported unsupported");
        end
    endtask

    protected virtual task check_optional_vendor(
        input bit [15:0] agent_caps);

        bit [7:0] response[$];
        bit [7:0] prot_cap_response[$];
        bit [7:0] empty_payload[$];
        bit [7:0] payload[$];
        bit [15:0] updated_agent_caps;
        bit [7:0] unused_cms_count;
        bit [7:0] unused_heartbeat_period;
        bit identification_disabled;
        bit identification_enabled;
        bit vendor_disabled;
        if (agent_caps[OCP_CAP_VENDOR]) begin
            ocp_read(OCP_CMD_VENDOR, response,
                     "OCP_CMD_009_VENDOR_ADVERTISED");
            if ((response.size() < OCP_SPEC_MIN_LEN_VENDOR) ||
                (response.size() > wMaxRdTransferSize)) begin
                `uvm_error("OCP_CMD",
                    $sformatf("Advertised VENDOR response length=%0d is outside 1..%0d.",
                              response.size(), wMaxRdTransferSize))
            end
            if ((response.size() == 1) &&
                (response[0] != VENDOR_DEFAULT_DATA)) begin
                `uvm_error("OCP_CMD",
                    $sformatf("Advertised VENDOR data=0x%02h, expected firmware-programmed 0x%02h.",
                              response[0], VENDOR_DEFAULT_DATA))
            end
            mark_check("OCP_CMD_009",
                "advertised VENDOR transport accepted; payload is vendor-defined");

            // Firmware owns Identification advertisement. Disable it while
            // VENDOR remains available as the directed policy request channel.
            payload = '{IDENTIFICATION_DISABLE_TOKEN};
            ocp_write(
                OCP_CMD_VENDOR, payload,
                "OCP_CMD_002_DEVICE_ID_DISABLE");
            identification_disabled = 1'b0;
            repeat (100) begin
                ocp_read(
                    OCP_CMD_PROT_CAP, prot_cap_response,
                    "OCP_CMD_002_DEVICE_ID_DISABLE_POLL");
                if (prot_cap_response.size() >
                        OCP_OFF_PC_AGENT_CAPS_HI) begin
                    updated_agent_caps = {
                        prot_cap_response[OCP_OFF_PC_AGENT_CAPS_HI],
                        prot_cap_response[OCP_OFF_PC_AGENT_CAPS_LO]};
                    if (!updated_agent_caps[OCP_CAP_IDENTIFICATION]) begin
                        identification_disabled = 1'b1;
                        break;
                    end
                end
                #1us;
            end
            if (!identification_disabled) begin
                `uvm_error("OCP_CMD",
                    "Firmware did not clear Identification capability after the disable token.")
            end
            empty_payload.delete();
            ocp_expect_protocol_error(
                1'b1, OCP_CMD_DEVICE_ID, empty_payload,
                OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND,
                "OCP_CMD_002_DEVICE_ID_DISABLED_IN", 1'b1);
            mark_check("OCP_CMD_002",
                "firmware-disabled DEVICE_ID rejected");

            payload = '{IDENTIFICATION_ENABLE_TOKEN};
            ocp_write(
                OCP_CMD_VENDOR, payload,
                "OCP_CMD_002_DEVICE_ID_ENABLE");
            identification_enabled = 1'b0;
            repeat (100) begin
                ocp_read(
                    OCP_CMD_PROT_CAP, prot_cap_response,
                    "OCP_CMD_002_DEVICE_ID_ENABLE_POLL");
                if (prot_cap_response.size() >
                        OCP_OFF_PC_AGENT_CAPS_HI) begin
                    updated_agent_caps = {
                        prot_cap_response[OCP_OFF_PC_AGENT_CAPS_HI],
                        prot_cap_response[OCP_OFF_PC_AGENT_CAPS_LO]};
                    if (updated_agent_caps[OCP_CAP_IDENTIFICATION]) begin
                        identification_enabled = 1'b1;
                        break;
                    end
                end
                #1us;
            end
            if (!identification_enabled) begin
                `uvm_error("OCP_CMD",
                    "Firmware did not restore Identification capability after the enable token.")
            end

            // Restore the firmware-owned VENDOR payload before independently
            // disabling VENDOR command support.
            payload = '{VENDOR_DEFAULT_DATA};
            ocp_write(
                OCP_CMD_VENDOR, payload,
                "OCP_CMD_009_VENDOR_DATA_RESTORE");

            // This directed firmware contract proves that capability
            // advertisement controls both VENDOR directions at runtime.
            payload = '{VENDOR_DISABLE_TOKEN};
            ocp_write(OCP_CMD_VENDOR, payload, "OCP_CMD_009_VENDOR_DISABLE");
            vendor_disabled = 1'b0;
            repeat (100) begin
                prot_cap_read_and_check(
                    updated_agent_caps,
                    unused_cms_count,
                    unused_heartbeat_period);
                if (!updated_agent_caps[OCP_CAP_VENDOR]) begin
                    vendor_disabled = 1'b1;
                    break;
                end
                #1us;
            end
            if (!vendor_disabled) begin
                `uvm_error("OCP_CMD",
                    "Firmware did not clear VENDOR capability after the disable token.")
            end

            empty_payload.delete();
            ocp_expect_protocol_error(
                1'b1, OCP_CMD_VENDOR, empty_payload,
                OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND,
                "OCP_CMD_009_VENDOR_DISABLED_IN", 1'b1);
            payload = '{VENDOR_DEFAULT_DATA};
            ocp_expect_protocol_error(
                1'b0, OCP_CMD_VENDOR, payload,
                OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND,
                "OCP_CMD_009_VENDOR_DISABLED_OUT", 1'b1);
            mark_check("OCP_CMD_009",
                "firmware-disabled VENDOR rejected in both directions");
        end else begin
            empty_payload.delete();
            ocp_expect_protocol_error(
                1'b1, OCP_CMD_VENDOR, empty_payload,
                OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND,
                "OCP_CMD_009_VENDOR_UNADVERTISED", 1'b1);
            mark_check("OCP_CMD_009",
                "unadvertised VENDOR command reported unsupported");
        end
    endtask

    protected virtual task check_optional_indirect_commands(
        input bit [15:0] agent_caps);

        bit [7:0] response[$];
        bit [7:0] empty_payload[$];

        if (agent_caps[OCP_CAP_INDIRECT_CTRL]) begin
            ocp_read(OCP_CMD_INDIRECT_CTRL, response,
                     "OCP_INDIRECT_CTRL_ADVERTISED");
            check_fixed_length(
                response, OCP_SPEC_LEN_INDIRECT_CTRL, "INDIRECT_CTRL");

            ocp_read(OCP_CMD_INDIRECT_STATUS, response,
                     "OCP_INDIRECT_STATUS_ADVERTISED");
            check_fixed_length(
                response, OCP_SPEC_LEN_INDIRECT_STATUS, "INDIRECT_STATUS");
            if ((response.size() == OCP_SPEC_LEN_INDIRECT_STATUS) &&
                ((response[0] & 8'hE0) != 8'h00)) begin
                `uvm_error("OCP_CMD",
                    $sformatf("INDIRECT_STATUS reserved bits are nonzero: 0x%02h.",
                              response[0]))
            end
        end else begin
            empty_payload.delete();
            ocp_expect_protocol_error(
                1'b1, OCP_CMD_INDIRECT_CTRL, empty_payload,
                OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND,
                "OCP_INDIRECT_CTRL_UNADVERTISED", 1'b1);
        end

        if (agent_caps[OCP_CAP_INDIRECT_FIFO]) begin
            ocp_read(OCP_CMD_INDIRECT_FIFO_CTRL, response,
                     "OCP_INDIRECT_FIFO_CTRL_ADVERTISED");
            check_fixed_length(
                response, OCP_SPEC_LEN_INDIRECT_FIFO_CTRL,
                "INDIRECT_FIFO_CTRL");
            indirect_fifo_status_read_and_check();
        end else begin
            empty_payload.delete();
            ocp_expect_protocol_error(
                1'b1, OCP_CMD_INDIRECT_FIFO_CTRL, empty_payload,
                OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND,
                "OCP_INDIRECT_FIFO_CTRL_UNADVERTISED", 1'b1);
        end
    endtask

    protected virtual task check_device_reset_command(
        input bit [15:0] agent_caps);

        bit [7:0] response[$];
        bit [7:0] empty_payload[$];
        bit reset_capability;

        reset_capability =
            agent_caps[OCP_CAP_FORCED_RECOVERY] ||
            agent_caps[OCP_CAP_MGMT_RESET] ||
            agent_caps[OCP_CAP_DEVICE_RESET] ||
            agent_caps[OCP_CAP_INTERFACE_ISOLATION] ||
            agent_caps[OCP_CAP_FLASHLESS_BOOT];

        if (reset_capability) begin
            ocp_read(OCP_CMD_DEVICE_RESET, response,
                     "OCP_DEVICE_RESET_READ_ONLY_PROBE");
            check_fixed_length(
                response, OCP_SPEC_LEN_DEVICE_RESET, "DEVICE_RESET");
        end else begin
            empty_payload.delete();
            ocp_expect_protocol_error(
                1'b1, OCP_CMD_DEVICE_RESET, empty_payload,
                OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND,
                "OCP_DEVICE_RESET_UNADVERTISED", 1'b1);
        end
    endtask

    protected virtual task check_recovery_ctrl_read();
        bit [7:0] response[$];

        ocp_read(OCP_CMD_RECOVERY_CTRL, response,
                 "OCP_RECOVERY_CTRL_READ");
        check_fixed_length(
            response, OCP_SPEC_LEN_RECOVERY_CTRL, "RECOVERY_CTRL");
        if (response.size() == OCP_SPEC_LEN_RECOVERY_CTRL) begin
            if (response[OCP_OFF_RC_IMG_SEL] > 8'h02) begin
                `uvm_error("OCP_CMD",
                    $sformatf("RECOVERY_CTRL image selection 0x%02h is reserved.",
                              response[OCP_OFF_RC_IMG_SEL]))
            end
            if ((response[OCP_OFF_RC_ACTIVATE] != 8'h00) &&
                (response[OCP_OFF_RC_ACTIVATE] !=
                    OCP_RC_ACTIVATE_CODE)) begin
                `uvm_error("OCP_CMD",
                    $sformatf("RECOVERY_CTRL activation value 0x%02h is reserved.",
                              response[OCP_OFF_RC_ACTIVATE]))
            end
        end
    endtask

    protected virtual function void report_executed_checks();
        string test_id;
        string summary;

        summary = "";
        if (checks_executed.first(test_id)) begin
            do begin
                summary = {summary,
                    $sformatf(" %s=%0d;", test_id,
                              checks_executed[test_id])};
            end while (checks_executed.next(test_id));
        end
        `uvm_info("OCP_CMD_CHECK",
            {"OCP_CMD_IMPLEMENTATION_SUMMARY", summary},
            UVM_NONE)
    endfunction

    virtual task body();
        bit [15:0] agent_caps;
        bit [7:0] cms_count;
        bit [7:0] heartbeat_period;
        bit [7:0] device_status[$];
        bit [7:0] rejected_write[$];

        initialize_ocp_transport();

        prot_cap_read_and_check(
            agent_caps, cms_count, heartbeat_period);
        mark_check("OCP_CMD_001",
            $sformatf("PROT_CAP spec invariants checked caps=0x%04h cms_count=%0d",
                      agent_caps, cms_count));

        device_id_read_and_check(EXPECTED_DEVICE_ID);
        mark_check("OCP_CMD_002",
            "firmware-programmed DEVICE_ID readback and host-RO policy checked");
        rejected_write = '{8'h00};
        ocp_expect_protocol_error(
            1'b0, OCP_CMD_DEVICE_ID, rejected_write,
            OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND,
            "OCP_CMD_002_DEVICE_ID_HOST_WRITE", 1'b1);

        device_status_read_and_check(
            device_status, "OCP_CMD_011_DEVICE_STATUS");
        check_heartbeat_behavior(heartbeat_period);

        // OCP Recovery v1.1 Sec 9.1 requires a write to a read-only command
        // to set Unsupported/Write Command in DEVICE_STATUS. The first RA
        // DEVICE_STATUS read observes the error and the second proves the
        // clear-on-read behavior required by Sec 9.1 and Sec 9.2.
        rejected_write = '{8'h00};
        ocp_expect_protocol_error(
            1'b0, OCP_CMD_PROT_CAP, rejected_write,
            OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND,
            "OCP_CMD_004_PROT_CAP_WRITE_TO_RO", 1'b0);
        mark_check("OCP_CMD_004",
            "write-to-RO error latched and cleared by consecutive RA reads");

        check_optional_hw_status(agent_caps);
        check_optional_vendor(agent_caps);

        // Non-destructive command handling probes. Stateful data transfers,
        // reset writes, FIFO writes, and recovery activation are covered by
        // the OCP_CMD flow, OCP_FIFO, and OCP_FLOW sequences.
        check_device_reset_command(agent_caps);
        check_recovery_ctrl_read();
        recovery_status_read_and_check();
        check_optional_indirect_commands(agent_caps);

        wait_mcu_axi_idle_before_finish("OCP_CMD_HANDLING_FINISH");
        publish_transfer_count();
        report_executed_checks();
        #1us;
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_CMD_HANDLING_SEQUENCE_SV
