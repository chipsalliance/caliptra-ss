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

`ifndef CALIPTRA_SS_USB_OCP_W1DC_ACCESS_SEMANTICS_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_W1DC_ACCESS_SEMANTICS_SEQUENCE_SV

// =============================================================================
// caliptra_ss_usb_ocp_w1dc_access_semantics_sequence
//
// Verifies OCP Recovery v1.1 Sec 9.2 Write-1-Device-Clears source
// qualification for DEVICE_RESET.RESET_CTRL and INDIRECT_FIFO_CTRL.RESET.
//
// Choreography:
//  1. Initialize transport, read PROT_CAP live. Wait firmware READY.
//  2. While firmware writes DEVICE_RESET.RESET_CTRL via CPUif:
//     - Monitor subsystem_reset_n remains high throughout
//       (CPUif write stores the value; no RA reset action).
//  3. Wait FW_DEVICE_RESET_STORED and FW_DEVICE_RESET_CLEARED.
//  4. If INDIRECT_FIFO capability advertised:
//     a. Program FIFO image size 2, write two deterministic DWORDs.
//     b. Wait FIFO_NONEMPTY_SEEN.
//     c. USB write INDIRECT_FIFO_CTRL RESET=1.
//     d. Read ctrl back; require RESET byte zero (device cleared).
//     e. Read status; require empty/W==R.
//     f. Wait USB_FIFO_RESET_OBSERVED (CALIPTRA_STATUS is diagnostic only).
//     g. Refill FIFO with two DWORDs. Wait FW_FIFO_RESET_OBSERVED.
//     h. Independently read ctrl/status; require RESET zero and empty.
//  5. DEVICE_RESET RA action (capability conditional):
//     - If DEVICE_RESET capability bit zero, require unsupported error.
//     - If advertised, USB write RESET_CTRL=1; boundedly observe reset_n.
//       Readback requires RESET_CTRL zero. If reset_n does not deassert,
//       report that the platform reset action is not integrated.
//     - Forced/Flashless capabilities: if advertised, issue write and
//       require acceptance and report when the next-reset platform action
//       cannot be observed. If de-advertised, require unsupported.
// =============================================================================

class caliptra_ss_usb_ocp_w1dc_access_semantics_sequence
    extends caliptra_ss_usb_ocp_recovery_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_w1dc_access_semantics_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    protected virtual caliptra_ss_usb_ocp_access_semantics_if sem_vif;

    localparam int unsigned SEM_MAX_POLLS   = 2000;
    localparam time         SEM_POLL_PERIOD = 10us;

    // How long to observe subsystem_reset_n after a DEVICE_RESET write.
    localparam int unsigned RESET_OBS_POLLS  = 50;
    localparam time         RESET_OBS_PERIOD = 10us;

    // Deterministic FIFO DWORDs for W1DC fill phases.
    localparam bit [31:0] FIFO_DWORD_0 = 32'hA5A5_C0DE;
    localparam bit [31:0] FIFO_DWORD_1 = 32'hDEAD_BEEF;

    function new(string name =
        "caliptra_ss_usb_ocp_w1dc_access_semantics_sequence");
        super.new(name);
    endfunction

    protected virtual function bit get_sem_vif();
        if (!uvm_config_db#(
                virtual caliptra_ss_usb_ocp_access_semantics_if)::get(
                    null, "uvm_test_top.env",
                    "ocp_access_semantics_if", sem_vif)) begin
            `uvm_fatal("W1DC_SEQ",
                "ocp_access_semantics_if not found in config_db")
            return 1'b0;
        end
        return 1'b1;
    endfunction

    protected virtual task wait_fw_state(
        input logic [7:0] target_state,
        input string      label);

        bit found;
        sem_vif.wait_for_fw_state_bounded(
            target_state, SEM_MAX_POLLS, SEM_POLL_PERIOD, found);
        if (!found) begin
            `uvm_fatal("W1DC_SEQ",
                $sformatf("%s: firmware state 0x%02h not observed within timeout.",
                          label, target_state))
        end
    endtask

    // -------------------------------------------------------------------------
    // write_fifo_dwords: write two deterministic DWORDs to the FIFO.
    // -------------------------------------------------------------------------
    protected virtual task write_fifo_dwords(input string label);
        bit [7:0] payload[$];

        // Each DWORD is written as a 4-byte OUT transfer to INDIRECT_FIFO_DATA.
        payload = '{FIFO_DWORD_0[7:0],  FIFO_DWORD_0[15:8],
                    FIFO_DWORD_0[23:16], FIFO_DWORD_0[31:24]};
        ocp_write(OCP_CMD_INDIRECT_FIFO_DATA, payload,
                  {label, "_FIFO_DW0"});

        payload = '{FIFO_DWORD_1[7:0],  FIFO_DWORD_1[15:8],
                    FIFO_DWORD_1[23:16], FIFO_DWORD_1[31:24]};
        ocp_write(OCP_CMD_INDIRECT_FIFO_DATA, payload,
                  {label, "_FIFO_DW1"});
    endtask

    // -------------------------------------------------------------------------
    // check_fifo_reset_usb: after USB INDIRECT_FIFO_CTRL RESET=1,
    // read back ctrl and status and verify RESET cleared + FIFO empty.
    // -------------------------------------------------------------------------
    protected virtual task check_fifo_reset_usb(input string label);
        bit [7:0]  ctrl_resp[$];
        bit [7:0]  status_resp[$];
        bit        fifo_empty;
        bit        fifo_full;
        bit [7:0]  region_type;
        bit [31:0] write_index;
        bit [31:0] read_index;
        bit [31:0] fifo_size;
        bit [31:0] max_xfer;

        ocp_read(OCP_CMD_INDIRECT_FIFO_CTRL, ctrl_resp,
                 {label, "_CTRL_RB"});
        if (ctrl_resp.size() != OCP_SPEC_LEN_INDIRECT_FIFO_CTRL) begin
            `uvm_error("W1DC_SEQ",
                $sformatf("%s: INDIRECT_FIFO_CTRL response length=%0d, expected %0d.",
                          label, ctrl_resp.size(),
                          OCP_SPEC_LEN_INDIRECT_FIFO_CTRL))
        end else begin
            if (ctrl_resp[OCP_OFF_IFC_RESET] !== 8'h00) begin
                `uvm_error("W1DC_SEQ",
                    $sformatf("%s: INDIRECT_FIFO_CTRL RESET byte=0x%02h after USB RESET, expected 0x00.",
                              label, ctrl_resp[OCP_OFF_IFC_RESET]))
            end
        end

        indirect_fifo_status_read(
            status_resp, fifo_empty, fifo_full, region_type,
            write_index, read_index, fifo_size, max_xfer,
            {label, "_STATUS"});
        if (!fifo_empty) begin
            `uvm_error("W1DC_SEQ",
                $sformatf("%s: FIFO not empty after USB RESET.", label))
        end
        if (write_index !== read_index) begin
            `uvm_error("W1DC_SEQ",
                $sformatf("%s: write_index=%0d != read_index=%0d after USB RESET.",
                          label, write_index, read_index))
        end
        `uvm_info("W1DC_SEQ",
            $sformatf("%s: USB RESET verified: empty=%0b W=%0d R=%0d",
                      label, fifo_empty, write_index, read_index),
            UVM_MEDIUM)
    endtask

    // -------------------------------------------------------------------------
    // check_fifo_reset_fw: after firmware CPUif INDIRECT_FIFO_CTRL RESET,
    // independently verify ctrl RESET zero and status empty/W==R.
    // -------------------------------------------------------------------------
    protected virtual task check_fifo_reset_fw(input string label);
        bit [7:0]  ctrl_resp[$];
        bit [7:0]  status_resp[$];
        bit        fifo_empty;
        bit        fifo_full;
        bit [7:0]  region_type;
        bit [31:0] write_index;
        bit [31:0] read_index;
        bit [31:0] fifo_size;
        bit [31:0] max_xfer;

        ocp_read(OCP_CMD_INDIRECT_FIFO_CTRL, ctrl_resp,
                 {label, "_CTRL_RB"});
        if (ctrl_resp.size() != OCP_SPEC_LEN_INDIRECT_FIFO_CTRL) begin
            `uvm_error("W1DC_SEQ",
                $sformatf("%s: INDIRECT_FIFO_CTRL response length=%0d, expected %0d.",
                          label, ctrl_resp.size(),
                          OCP_SPEC_LEN_INDIRECT_FIFO_CTRL))
        end else begin
            if (ctrl_resp[OCP_OFF_IFC_RESET] !== 8'h00) begin
                `uvm_error("W1DC_SEQ",
                    $sformatf("%s: INDIRECT_FIFO_CTRL RESET byte=0x%02h after FW RESET, expected 0x00.",
                              label, ctrl_resp[OCP_OFF_IFC_RESET]))
            end
        end

        indirect_fifo_status_read(
            status_resp, fifo_empty, fifo_full, region_type,
            write_index, read_index, fifo_size, max_xfer,
            {label, "_STATUS"});
        if (!fifo_empty) begin
            `uvm_error("W1DC_SEQ",
                $sformatf("%s: FIFO not empty after FW RESET.", label))
        end
        if (write_index !== read_index) begin
            `uvm_error("W1DC_SEQ",
                $sformatf("%s: write_index=%0d != read_index=%0d after FW RESET.",
                          label, write_index, read_index))
        end
        `uvm_info("W1DC_SEQ",
            $sformatf("%s: FW RESET verified: empty=%0b W=%0d R=%0d",
                      label, fifo_empty, write_index, read_index),
            UVM_MEDIUM)
    endtask

    virtual task body();
        bit [15:0]  agent_caps;
        bit [7:0]   cms_count;
        bit [7:0]   heartbeat_period;
        bit [7:0]   payload[$];
        bit [7:0]   empty_payload[$];
        bit         reset_n_stable;
        bit         reset_deasserted;
        bit         reset_reasserted;
        bit [7:0]   dr_resp[$];
        caliptra_ss_usb_ocp_xfer_result_e result;
        caliptra_ss_usb_ocp_xfer_result_e rb_result;
        uvm_event fifo_model_reset_event;

        if (!get_sem_vif()) return;

        initialize_ocp_transport();
        prot_cap_read_and_check(agent_caps, cms_count, heartbeat_period);

        // Wait firmware READY.
        wait_fw_state(W1DC_SEM_STATE_READY, "W1DC_READY");
        `uvm_info("W1DC_SEQ", "Firmware READY observed.", UVM_NONE)

        sem_vif.clear_subsystem_reset_seen();

        // Use a standard negative RA command as a capability-independent,
        // protocol-visible start trigger for the firmware CPUif checks.
        payload = '{8'h00};
        ocp_try_write(OCP_CMD_PROT_CAP, payload, result,
                      "W1DC_FW_START_TRIGGER");

        // -----------------------------------------------------------------
        // Monitor subsystem_reset_n during CPUif DEVICE_RESET phases.
        // It must remain high throughout; firmware write stores but does
        // not trigger the RA reset action (OCP Recovery v1.1 Sec 9.2).
        // -----------------------------------------------------------------

        // -----------------------------------------------------------------
        // INDIRECT_FIFO capability conditional checks.
        // -----------------------------------------------------------------

        reset_n_stable = 1'b1;
        wait_fw_state(W1DC_SEM_STATE_FW_DEVICE_RESET_STORED,
                      "W1DC_FW_DR_STORED");

        // Clear the start-trigger protocol error through the RA path.
        begin
            bit [7:0] device_status[$];
            device_status_read_and_check(
                device_status, "W1DC_START_TRIGGER_CLEAR");
            wait_fw_state(W1DC_SEM_STATE_FW_DEVICE_RESET_CLEARED,
                          "W1DC_FW_DR_CLEARED");
            device_status_read_and_check(
                device_status, "W1DC_START_TRIGGER_CLEAR_CONFIRM");
        end

        if (!sem_vif.subsystem_reset_n ||
            sem_vif.subsystem_reset_seen) begin
            `uvm_error("W1DC_SEQ",
                {"subsystem_reset_n changed during CPUif DEVICE_RESET writes. ",
                 "CPUif writes must not trigger Recovery Agent reset action."})
            reset_n_stable = 1'b0;
        end
        if (reset_n_stable) begin
            `uvm_info("W1DC_SEQ",
                "subsystem_reset_n remained stable during CPUif DEVICE_RESET writes.",
                UVM_NONE)
        end

        if (agent_caps[OCP_CAP_INDIRECT_FIFO]) begin

            // Program FIFO image size for the reset semantics checks.
            indirect_fifo_ctrl_write(8'h00, 1'b0, 32'd2,
                                     "W1DC_FIFO_SETUP");

            // Write two deterministic DWORDs.
            write_fifo_dwords("W1DC_FIFO_FILL_USB");

            // Wait firmware FIFO_NONEMPTY_SEEN.
            wait_fw_state(W1DC_SEM_STATE_FIFO_NONEMPTY_SEEN,
                          "W1DC_FIFO_NONEMPTY");

            // USB write INDIRECT_FIFO_CTRL RESET=1.
            indirect_fifo_ctrl_write(8'h00, 1'b1, 32'd0,
                                     "W1DC_FIFO_USB_RESET");

            // Verify RESET self-cleared and FIFO is empty with W==R.
            check_fifo_reset_usb("W1DC_USB_RESET");

            // Wait firmware USB_FIFO_RESET_OBSERVED.
            // CALIPTRA_STATUS data from firmware is diagnostic only;
            // it is not an OCP-specified expected value.
            wait_fw_state(W1DC_SEM_STATE_USB_FIFO_RESET_OBSERVED,
                          "W1DC_USB_FIFO_RESET_OBS");
            `uvm_info("W1DC_SEQ",
                $sformatf("USB_FIFO_RESET_OBSERVED: caliptra_status_region_reset=%0b (diagnostic)",
                          sem_vif.get_fw_data()),
                UVM_MEDIUM)

            // Refill FIFO (firmware is waiting for this).
            indirect_fifo_ctrl_write(8'h00, 1'b0, 32'd2,
                                     "W1DC_FIFO_REFILL_SETUP");
            write_fifo_dwords("W1DC_FIFO_REFILL");

            // Wait firmware FW_FIFO_RESET_OBSERVED (firmware did the reset).
            wait_fw_state(W1DC_SEM_STATE_FW_FIFO_RESET_OBSERVED,
                          "W1DC_FW_FIFO_RESET_OBS");

            // Firmware reset is not a USB transfer, so explicitly synchronize
            // the passive scoreboard model at the externally observed reset
            // completion boundary before the next status read.
            fifo_model_reset_event =
                uvm_event_pool::get_global("ocp_fifo_model_reset");
            fifo_model_reset_event.trigger();

            // Independently verify: USB read ctrl/status after FW reset.
            check_fifo_reset_fw("W1DC_FW_RESET_VERIFY");

        end else begin
            wait_fw_state(W1DC_SEM_STATE_FIFO_UNSUPPORTED,
                          "W1DC_FIFO_UNSUPPORTED_FW");
            // FIFO capability not advertised; verify unsupported behavior.
            empty_payload.delete();
            ocp_expect_protocol_error(
                1'b1, OCP_CMD_INDIRECT_FIFO_CTRL, empty_payload,
                OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND,
                "W1DC_FIFO_UNADVERTISED");
            `uvm_info("W1DC_SEQ",
                "INDIRECT_FIFO not advertised; unsupported-command error verified.",
                UVM_NONE)
        end

        // Check next-reset capabilities before the potentially disruptive
        // immediate DEVICE_RESET action.
        if (agent_caps[OCP_CAP_FORCED_RECOVERY]) begin
            payload = '{8'h00, 8'h0F, 8'h00};
            ocp_try_write(OCP_CMD_DEVICE_RESET, payload, result,
                          "W1DC_FORCED_RECOV_0F");
            if (result == OCP_XFER_ABORTED) begin
                `uvm_error("W1DC_SEQ",
                    "FORCED_RECOVERY write aborted before platform behavior could be assessed.")
            end else begin
                `uvm_error("W1DC_SEQ",
                    {"INTEGRATION_INCOMPLETE: FORCED_RECOVERY is advertised, ",
                     "but this environment has no architectural observation ",
                     "point for its next-platform-reset action."})
            end
        end else begin
            payload = '{8'h00, 8'h0F, 8'h00};
            ocp_expect_protocol_error(
                1'b0, OCP_CMD_DEVICE_RESET, payload,
                OCP_PROTOCOL_ERROR_UNSUPPORTED_PARAMETER,
                "W1DC_FORCED_RECOVERY_UNADVERTISED");
        end

        if (agent_caps[OCP_CAP_FLASHLESS_BOOT]) begin
            payload = '{8'h00, 8'h0E, 8'h00};
            ocp_try_write(OCP_CMD_DEVICE_RESET, payload, result,
                          "W1DC_FLASHLESS_0E");
            if (result == OCP_XFER_ABORTED) begin
                `uvm_error("W1DC_SEQ",
                    "FLASHLESS_BOOT write aborted before platform behavior could be assessed.")
            end else begin
                `uvm_error("W1DC_SEQ",
                    {"INTEGRATION_INCOMPLETE: FLASHLESS_BOOT is advertised, ",
                     "but this environment has no architectural observation ",
                     "point for its next-platform-reset action."})
            end
        end else begin
            payload = '{8'h00, 8'h0E, 8'h00};
            ocp_expect_protocol_error(
                1'b0, OCP_CMD_DEVICE_RESET, payload,
                OCP_PROTOCOL_ERROR_UNSUPPORTED_PARAMETER,
                "W1DC_FLASHLESS_UNADVERTISED");
        end

        // -----------------------------------------------------------------
        // DEVICE_RESET RA action (done last due to possible disruption).
        // -----------------------------------------------------------------

        if (!agent_caps[OCP_CAP_DEVICE_RESET]) begin
            // Capability not advertised; verify unsupported command on read.
            empty_payload.delete();
            ocp_expect_protocol_error(
                1'b1, OCP_CMD_DEVICE_RESET, empty_payload,
                OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND,
                "W1DC_DEVICE_RESET_UNADVERTISED");
            `uvm_info("W1DC_SEQ",
                "DEVICE_RESET not advertised; unsupported-command error verified.",
                UVM_NONE)

        end else begin
            // DEVICE_RESET advertised; USB write RESET_CTRL=1.
            sem_vif.clear_subsystem_reset_seen();
            payload = '{8'h01, 8'h00, 8'h00};
            ocp_write(OCP_CMD_DEVICE_RESET, payload, "W1DC_USB_DR_WRITE");

            // Observe the architectural reset output to prove that the
            // Recovery Agent write reaches the platform reset consumer.
            reset_deasserted = 1'b0;
            for (int unsigned i = 0; i < RESET_OBS_POLLS; i++) begin
                if (!sem_vif.subsystem_reset_n ||
                    sem_vif.subsystem_reset_seen) begin
                    reset_deasserted = 1'b1;
                    break;
                end
                #(RESET_OBS_PERIOD);
            end
            if (!reset_deasserted) begin
                `uvm_error("W1DC_SEQ",
                    {"INTEGRATION_INCOMPLETE: subsystem_reset_n did not deassert ",
                     "after USB DEVICE_RESET write. Platform reset routing from USB OCP ",
                     "RESET_CTRL to the subsystem reset output is incomplete ",
                     "(OCP Recovery v1.1 Sec 9.2 DEVICE_RESET)."})
            end else begin
                `uvm_info("W1DC_SEQ",
                    "subsystem_reset_n deasserted after USB DEVICE_RESET write.",
                    UVM_NONE)

                reset_reasserted = 1'b0;
                for (int unsigned i = 0; i < RESET_OBS_POLLS; i++) begin
                    if (sem_vif.subsystem_reset_n === 1'b1) begin
                        reset_reasserted = 1'b1;
                        break;
                    end
                    #(RESET_OBS_PERIOD);
                end
                if (!reset_reasserted) begin
                    `uvm_error("W1DC_SEQ",
                        "subsystem_reset_n did not reassert after USB DEVICE_RESET.")
                end else begin
                    initialize_ocp_transport();
                end
            end

            // RESET_CTRL must return to zero after device consumption. If the
            // reset disrupted USB, transport was reinitialized above.
            ocp_try_read(OCP_CMD_DEVICE_RESET, dr_resp, rb_result,
                         "W1DC_USB_DR_READBACK");
            if (rb_result == OCP_XFER_SUCCESS) begin
                if (dr_resp.size() != OCP_SPEC_LEN_DEVICE_RESET) begin
                    `uvm_error("W1DC_SEQ",
                        $sformatf("DEVICE_RESET response length=%0d, expected %0d.",
                                  dr_resp.size(),
                                  OCP_SPEC_LEN_DEVICE_RESET))
                end else if (dr_resp[OCP_OFF_DR_RESET_CONTROL] !== 8'h00) begin
                    `uvm_error("W1DC_SEQ",
                        $sformatf("DEVICE_RESET.RESET_CTRL readback=0x%02h after device consumption, expected 0x00.",
                                  dr_resp[OCP_OFF_DR_RESET_CONTROL]))
                end
            end else begin
                `uvm_error("W1DC_SEQ",
                    "DEVICE_RESET readback could not be completed after reset recovery.")
            end
        end

        publish_transfer_count();

        `uvm_info("W1DC_SEQ",
            "OCP_SEM_002 complete: W1DC source qualification checked.",
            UVM_NONE)

        #1us;
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_W1DC_ACCESS_SEMANTICS_SEQUENCE_SV
