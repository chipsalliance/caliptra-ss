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

`ifndef CALIPTRA_SS_USB_OCP_RECOVERY_ACTIVATION_ACCESS_SEMANTICS_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_RECOVERY_ACTIVATION_ACCESS_SEMANTICS_SEQUENCE_SV

// =============================================================================
// caliptra_ss_usb_ocp_recovery_activation_access_semantics_sequence
//
// Verifies the stored-level semantics of the OCP Recovery v1.1 Sec 9.2
// RECOVERY_CTRL.ACTIVATE field. The architectural activation indication is
// high whenever the stored field is 0x0F and low for every other value,
// regardless of whether USB or firmware wrote the field.
//
// Choreography:
//  1. Initialize transport. Wait firmware READY.
//  2. Firmware writes ACTIVATE=0x0F; require stored readback, high level, and
//     a positive edge. Firmware then clears it; require stored zero and low.
//  3. Initiate recovery: RECOVERY_CTRL Activate=0, program FIFO image size 1,
//     write deterministic DWORD 0xC0DE0000.
//  4. USB writes ACTIVATE=0x0F; require stored readback, high level, and a
//     fresh edge from the prior low baseline.
//  5. Firmware rewrites ACTIVATE=0x0F; require the level remains high.
//  6. Use a protocol-error set/clear handshake to release the final firmware
//     clear at a deterministic protocol-visible boundary.
//  7. Firmware writes ACTIVATE=0; require stored zero and low level.
// =============================================================================

class caliptra_ss_usb_ocp_recovery_activation_access_semantics_sequence
    extends caliptra_ss_usb_ocp_recovery_base_sequence;

    `uvm_object_utils(
        caliptra_ss_usb_ocp_recovery_activation_access_semantics_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    protected virtual caliptra_ss_usb_ocp_access_semantics_if sem_vif;

    localparam int unsigned SEM_MAX_POLLS    = 2000;
    localparam time         SEM_POLL_PERIOD  = 1us;

    localparam int unsigned ACT_MAX_POLLS   = 500;
    localparam time         ACT_POLL_PERIOD = 1us;

    // How many times to confirm ACTIVATE=0x0F remains pending.
    localparam int unsigned ACTIVATE_CONFIRM_READS = 3;

    // Deterministic FIFO DWORD; keep synchronized with the firmware check in
    // cptra_usb_ocp_recovery_activation_access_semantics.c.
    localparam bit [31:0] ACT_FIFO_DWORD = 32'hC0DE0000;

    function new(string name =
        "caliptra_ss_usb_ocp_recovery_activation_access_semantics_sequence");
        super.new(name);
    endfunction

    protected virtual function bit get_sem_vif();
        if (!uvm_config_db#(
                virtual caliptra_ss_usb_ocp_access_semantics_if)::get(
                    null, "uvm_test_top.env",
                    "ocp_access_semantics_if", sem_vif)) begin
            `uvm_fatal("RA_SEM_SEQ",
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
            `uvm_fatal("RA_SEM_SEQ",
                $sformatf("%s: firmware state 0x%02h not observed within timeout.",
                          label, target_state))
        end
    endtask

    protected virtual task wait_fw_post_ra_nonzero();
        bit found;

        found = 1'b0;
        for (int unsigned i = 0; i < SEM_MAX_POLLS; i++) begin
            if ((sem_vif.get_fw_state() ===
                    RA_SEM_STATE_FW_NONZERO_AFTER_RA) ||
                (sem_vif.get_fw_state() ===
                    RA_SEM_STATE_FW_ZERO_ARMED)) begin
                found = 1'b1;
                break;
            end
            #(SEM_POLL_PERIOD);
        end
        if (!found) begin
            `uvm_fatal("RA_SEM_SEQ",
                "Firmware did not complete the post-RA ACTIVATE=0x0F write.")
        end
    endtask

    // -------------------------------------------------------------------------
    // read_recovery_ctrl_activate: read RECOVERY_CTRL and return ACTIVATE byte.
    // -------------------------------------------------------------------------
    protected virtual task read_recovery_ctrl_activate(
        output logic [7:0] activate_out,
        input  string      label);

        bit [7:0] resp[$];
        activate_out = 8'hFF;
        ocp_read(OCP_CMD_RECOVERY_CTRL, resp, label);
        if (resp.size() < (OCP_OFF_RC_ACTIVATE + 1)) begin
            `uvm_error("RA_SEM_SEQ",
                $sformatf("%s: RECOVERY_CTRL response too short (%0d bytes).",
                          label, resp.size()))
            return;
        end
        activate_out = resp[OCP_OFF_RC_ACTIVATE];
    endtask

    // -------------------------------------------------------------------------
    // Wait for the exact stored-value level rather than sampling in the same
    // delta cycle as a firmware state publication.
    // -------------------------------------------------------------------------
    protected virtual task wait_recovery_image_activated_level(
        input  bit expected_level,
        output bit reached_out);

        reached_out = 1'b0;
        for (int unsigned i = 0; i < ACT_MAX_POLLS; i++) begin
            if (sem_vif.recovery_image_activated === expected_level) begin
                reached_out = 1'b1;
                return;
            end
            #(ACT_POLL_PERIOD);
        end
    endtask

    virtual task body();
        bit [15:0]  agent_caps;
        bit [7:0]   cms_count;
        bit [7:0]   heartbeat_period;
        bit [7:0]   activate_val;
        bit         reached;
        bit [7:0]   payload[$];
        bit [7:0]   device_status[$];
        caliptra_ss_usb_ocp_xfer_result_e result;

        if (!get_sem_vif()) return;

        initialize_ocp_transport();
        prot_cap_read_and_check(agent_caps, cms_count, heartbeat_period);
        sem_vif.clear_i3c_recovery_seen();
        if (sem_vif.i3c_recovery_image_activated !== 1'b0) begin
            `uvm_fatal("OCP_ACTIVATION_LEVEL",
                "I3C image-activated source is not quiescent for USB route validation.")
        end

        // Wait firmware READY.
        wait_fw_state(RA_SEM_STATE_READY, "RA_SEM_READY");
        `uvm_info("RA_SEM_SEQ", "Firmware READY observed.", UVM_NONE)
        wait_recovery_image_activated_level(1'b0, reached);
        if (!reached) begin
            `uvm_fatal("OCP_ACTIVATION_LEVEL",
                "Activation level was not low before the first firmware 0x0F write.")
        end
        sem_vif.clear_recovery_image_activated_seen();

        // Program IMAGE_SIZE as a protocol-visible start trigger for firmware.
        // Data is not pushed until the pre-RA level checks end.
        indirect_fifo_ctrl_write(8'h00, 1'b0, 32'd1,
                                 "RA_SEM_FIFO_START_TRIGGER");

        wait_fw_state(RA_SEM_STATE_FW_NONZERO_STORED_PRE,
                      "RA_SEM_FW_NONZERO_PRE");
        read_recovery_ctrl_activate(
            activate_val, "RA_SEM_RC_FW_NONZERO_PRE");
        if (activate_val !== OCP_RC_ACTIVATE_CODE) begin
            `uvm_error("OCP_ACTIVATION_LEVEL",
                $sformatf("Firmware pre-RA ACTIVATE readback=0x%02h expected 0x%02h.",
                          activate_val, OCP_RC_ACTIVATE_CODE))
        end
        wait_recovery_image_activated_level(1'b1, reached);
        if (!reached || !sem_vif.recovery_image_activated_seen) begin
            `uvm_error("OCP_ACTIVATION_LEVEL",
                "Firmware pre-RA ACTIVATE=0x0F did not assert the activation level and edge.")
        end else begin
            `uvm_info("OCP_ACTIVATION_LEVEL",
                "Firmware pre-RA ACTIVATE=0x0F asserted the activation level.",
                UVM_NONE)
        end

        wait_fw_state(RA_SEM_STATE_FW_PRE_RA_CLEARED, "RA_SEM_FW_PRE_CLEARED");
        read_recovery_ctrl_activate(
            activate_val, "RA_SEM_RC_FW_PRE_CLEARED");
        if (activate_val !== 8'h00) begin
            `uvm_error("OCP_ACTIVATION_LEVEL",
                $sformatf("Firmware pre-RA clear readback=0x%02h expected 0x00.",
                          activate_val))
        end
        wait_recovery_image_activated_level(1'b0, reached);
        if (!reached) begin
            `uvm_error("OCP_ACTIVATION_LEVEL",
                "Firmware pre-RA ACTIVATE=0 did not deassert the activation level.")
        end
        sem_vif.clear_recovery_image_activated_seen();

        // -----------------------------------------------------------------
        // Initiate recovery: write RECOVERY_CTRL with Activate=0x00.
        // -----------------------------------------------------------------
        recovery_ctrl_write(8'h00, 8'h00, 1'b0, "RA_SEM_RC_INIT");

        // Write the deterministic one-DWORD image.
        payload = '{ACT_FIFO_DWORD[7:0],  ACT_FIFO_DWORD[15:8],
                    ACT_FIFO_DWORD[23:16], ACT_FIFO_DWORD[31:24]};
        ocp_write(OCP_CMD_INDIRECT_FIFO_DATA, payload, "RA_SEM_FIFO_DATA");

        // -----------------------------------------------------------------
        // USB write RECOVERY_CTRL ACTIVATE=0x0F.
        // -----------------------------------------------------------------
        recovery_ctrl_write(8'h00, 8'h00, 1'b1, "RA_SEM_RC_ACTIVATE");

        // -----------------------------------------------------------------
        // Wait RA_ACTIVATE_PENDING; confirm ACTIVATE=0x0F repeatedly.
        // -----------------------------------------------------------------
        wait_fw_state(RA_SEM_STATE_RA_ACTIVATE_PENDING,
                      "RA_SEM_RA_PENDING");

        for (int unsigned i = 0; i < ACTIVATE_CONFIRM_READS; i++) begin
            read_recovery_ctrl_activate(activate_val,
                $sformatf("RA_SEM_ACTIVATE_CONFIRM_%0d", i));
            if (activate_val !== OCP_RC_ACTIVATE_CODE) begin
                `uvm_error("RA_SEM_SEQ",
                    $sformatf({"RECOVERY_CTRL ACTIVATE confirm read %0d: ",
                               "got 0x%02h expected 0x%02h (pending)."},
                              i, activate_val, OCP_RC_ACTIVATE_CODE))
            end
        end

        wait_recovery_image_activated_level(1'b1, reached);
        if (!reached || !sem_vif.recovery_image_activated_seen) begin
            `uvm_error("OCP_ACTIVATION_LEVEL",
                "Recovery Agent ACTIVATE=0x0F did not assert a fresh activation level and edge.")
        end else begin
            `uvm_info("OCP_ACTIVATION_LEVEL",
                "Recovery Agent ACTIVATE=0x0F asserted the activation level.",
                UVM_NONE)
        end

        // Rewriting the activation code while already high maintains the
        // stored-value level and does not require another edge.
        wait_fw_post_ra_nonzero();
        read_recovery_ctrl_activate(
            activate_val, "RA_SEM_RC_FW_NONZERO_AFTER_RA");
        if (activate_val !== OCP_RC_ACTIVATE_CODE) begin
            `uvm_error("OCP_ACTIVATION_LEVEL",
                $sformatf("Firmware post-RA ACTIVATE readback=0x%02h expected 0x%02h.",
                          activate_val, OCP_RC_ACTIVATE_CODE))
        end
        wait_recovery_image_activated_level(1'b1, reached);
        if (!reached) begin
            `uvm_error("OCP_ACTIVATION_LEVEL",
                "Firmware post-RA ACTIVATE=0x0F did not maintain the activation level.")
        end else begin
            `uvm_info("OCP_ACTIVATION_LEVEL",
                "Firmware post-RA ACTIVATE=0x0F maintained the activation level.",
                UVM_NONE)
        end

        // -----------------------------------------------------------------
        // Arm the firmware zero write with a protocol-visible handshake.
        // Firmware waits for PROT_ERROR set, publishes FW_ZERO_ARMED, and
        // waits for the RA DEVICE_STATUS read to clear it.
        // -----------------------------------------------------------------
        payload = '{8'h00};
        ocp_try_write(
            OCP_CMD_PROT_CAP, payload, result, "RA_SEM_ZERO_ARM_TRIGGER");
        if (result == OCP_XFER_ABORTED) begin
            `uvm_fatal("RA_SEM_SEQ",
                "Pre-zero protocol-error trigger aborted.")
        end

        wait_fw_state(RA_SEM_STATE_FW_ZERO_ARMED, "RA_SEM_FW_ZERO_ARMED");
        wait_recovery_image_activated_level(1'b1, reached);
        if (!reached) begin
            `uvm_error("OCP_ACTIVATION_LEVEL",
                "Activation level deasserted before the firmware clear was released.")
        end

        // The RA read clears PROT_ERROR and releases firmware toward the zero
        // write. The exact DEVICE_STATUS length is checked by the command test;
        // this read is used only as the protocol-defined clear operation.
        ocp_read(
            OCP_CMD_DEVICE_STATUS, device_status, "RA_SEM_ZERO_ARM_RELEASE");

        // -----------------------------------------------------------------
        // Wait FW_ACTIVATE_CLEARED; verify RECOVERY_CTRL readback zero.
        // -----------------------------------------------------------------
        wait_fw_state(RA_SEM_STATE_FW_ACTIVATE_CLEARED,
                       "RA_SEM_FW_CLEARED");

        read_recovery_ctrl_activate(activate_val, "RA_SEM_RC_POST_CLEAR");
        if (activate_val !== 8'h00) begin
            `uvm_error("RA_SEM_SEQ",
                $sformatf("RECOVERY_CTRL ACTIVATE=0x%02h after firmware zero-write, expected 0x00.",
                          activate_val))
        end else begin
            `uvm_info("RA_SEM_SEQ",
                "RECOVERY_CTRL ACTIVATE=0x00 confirmed after firmware zero-write.",
                UVM_NONE)
        end

        wait_recovery_image_activated_level(1'b0, reached);
        if (!reached) begin
            `uvm_error("OCP_ACTIVATION_LEVEL",
                "Firmware ACTIVATE=0 did not deassert the activation level.")
        end else begin
            `uvm_info("OCP_ACTIVATION_LEVEL",
                "Firmware ACTIVATE=0 deasserted the activation level.",
                UVM_NONE)
        end

        if (sem_vif.i3c_recovery_image_activated_seen) begin
            `uvm_error("OCP_ACTIVATION_LEVEL",
                "I3C image-activated source asserted during USB route validation.")
        end

        wait_mcu_axi_idle_before_finish("OCP_ACTIVATION_LEVEL");
        publish_transfer_count();

        `uvm_info("RA_SEM_SEQ",
            "OCP_SEM_003 complete: recovery activation stored-level semantics checked.",
            UVM_NONE)

    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_RECOVERY_ACTIVATION_ACCESS_SEMANTICS_SEQUENCE_SV
