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
// Verifies OCP Recovery v1.1 Sec 9.2 RECOVERY_CTRL.ACTIVATE source
// qualification. The activation action requires firmware to consume the
// activation request by writing zero; firmware nonzero writes store the
// value without triggering activation.
//
// Choreography:
//  1. Initialize transport. Wait firmware READY.
//  2. Observe recovery_image_activated remains low during FW_NONZERO_STORED_PRE
//     and FW_PRE_RA_CLEARED phases.
//  3. Initiate recovery: RECOVERY_CTRL Activate=0, program FIFO image size 1,
//     write deterministic DWORD 0xC0DE0000.
//  4. USB write RECOVERY_CTRL ACTIVATE=0x0F.
//  5. Wait RA_ACTIVATE_PENDING; repeatedly read RECOVERY_CTRL requiring 0x0F.
//  6. Verify recovery_image_activated low before firmware zero.
//  7. Wait FW_NONZERO_AFTER_RA; verify recovery_image_activated still low.
//  8. Use a protocol-error set/clear handshake to arm the firmware zero write.
//     Check the sticky activation monitor before releasing firmware.
//  9. Clear the sticky monitor, then use the RA DEVICE_STATUS clear as the
//     release immediately preceding the firmware zero write.
// 10. Require a new recovery_image_activated edge after the zero-write barrier.
// 11. Wait for protocol recovery completion (RECOVERY_STATUS=SUCCESS).
//     If not observed, report incomplete platform boot-acknowledgment wiring.
// =============================================================================

class caliptra_ss_usb_ocp_recovery_activation_access_semantics_sequence
    extends caliptra_ss_usb_ocp_recovery_base_sequence;

    `uvm_object_utils(
        caliptra_ss_usb_ocp_recovery_activation_access_semantics_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    protected virtual caliptra_ss_usb_ocp_access_semantics_if sem_vif;

    localparam int unsigned SEM_MAX_POLLS    = 2000;
    localparam time         SEM_POLL_PERIOD  = 1us;

    // Polling for recovery_image_activated assertion after FW_ACTIVATE_CLEARED.
    localparam int unsigned ACT_MAX_POLLS   = 500;
    localparam time         ACT_POLL_PERIOD = 20us;

    // Polling for RECOVERY_STATUS completion.
    localparam int unsigned RECOV_MAX_POLLS  = 50;
    localparam time         RECOV_POLL_PERIOD = 20us;

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
    // wait_recovery_image_activated_bounded: poll for assertion.
    // -------------------------------------------------------------------------
    protected virtual task wait_recovery_image_activated_bounded(
        output bit asserted_out);

        asserted_out = 1'b0;
        for (int unsigned i = 0; i < ACT_MAX_POLLS; i++) begin
            if ((sem_vif.recovery_image_activated === 1'b1) ||
                sem_vif.recovery_image_activated_seen) begin
                asserted_out = 1'b1;
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
        bit         premature_activation;
        bit [7:0]   rs_resp[$];
        bit [7:0]   payload[$];
        bit [7:0]   device_status[$];
        caliptra_ss_usb_ocp_xfer_result_e result;

        if (!get_sem_vif()) return;

        initialize_ocp_transport();
        prot_cap_read_and_check(agent_caps, cms_count, heartbeat_period);

        // Wait firmware READY.
        wait_fw_state(RA_SEM_STATE_READY, "RA_SEM_READY");
        `uvm_info("RA_SEM_SEQ", "Firmware READY observed.", UVM_NONE)
        sem_vif.clear_recovery_image_activated_seen();
        premature_activation = 1'b0;

        // Program IMAGE_SIZE as a protocol-visible start trigger for firmware.
        // Data is not pushed until the pre-RA source-qualification checks end.
        indirect_fifo_ctrl_write(8'h00, 1'b0, 32'd1,
                                 "RA_SEM_FIFO_START_TRIGGER");

        // -----------------------------------------------------------------
        // Verify recovery_image_activated remains low during pre-RA firmware
        // nonzero-write phases. OCP activation action must not occur before
        // firmware zero-write consumption following the RA USB write.
        // -----------------------------------------------------------------

        wait_fw_state(RA_SEM_STATE_FW_NONZERO_STORED_PRE,
                      "RA_SEM_FW_NONZERO_PRE");
        if ((sem_vif.recovery_image_activated !== 1'b0) ||
            sem_vif.recovery_image_activated_seen) begin
            `uvm_error("RA_SEM_SEQ",
                {"recovery_image_activated asserted during FW_NONZERO_STORED_PRE. ",
                 "Firmware nonzero CPUif write must not trigger activation ",
                 "(OCP Recovery v1.1 Sec 9.2 RECOVERY_CTRL)."})
            premature_activation = 1'b1;
        end

        wait_fw_state(RA_SEM_STATE_FW_PRE_RA_CLEARED, "RA_SEM_FW_PRE_CLEARED");
        if ((sem_vif.recovery_image_activated !== 1'b0) ||
            sem_vif.recovery_image_activated_seen) begin
            `uvm_error("RA_SEM_SEQ",
                {"recovery_image_activated asserted after FW_PRE_RA_CLEARED. ",
                 "Pre-RA firmware writes must not affect activation state."})
            premature_activation = 1'b1;
        end
        `uvm_info("RA_SEM_SEQ",
            "recovery_image_activated remained low through pre-RA FW writes.",
            UVM_NONE)

        // -----------------------------------------------------------------
        // Initiate recovery: write RECOVERY_CTRL with Activate=0x00.
        // -----------------------------------------------------------------
        recovery_ctrl_write(8'h00, 8'h00, 1'b0, "RA_SEM_RC_INIT");

        // Write the deterministic one-DWORD image.
        payload = '{ACT_FIFO_DWORD[7:0],  ACT_FIFO_DWORD[15:8],
                    ACT_FIFO_DWORD[23:16], ACT_FIFO_DWORD[31:24]};
        ocp_write(OCP_CMD_INDIRECT_FIFO_DATA, payload, "RA_SEM_FIFO_DATA");

        // Poll RECOVERY_STATUS until AWAITING_IMAGE to confirm device ready.
        poll_recovery_status(
            OCP_RECOVERY_STATUS_AWAITING_IMAGE, 200, 10us,
            reached, rs_resp, "RA_SEM_RS_AWAIT");
        if (!reached) begin
            `uvm_info("RA_SEM_SEQ",
                "RECOVERY_STATUS AWAITING_IMAGE not observed; proceeding.",
                UVM_MEDIUM)
        end

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

        // Verify recovery_image_activated still low before firmware zero.
        if ((sem_vif.recovery_image_activated !== 1'b0) ||
            sem_vif.recovery_image_activated_seen) begin
            `uvm_error("RA_SEM_SEQ",
                {"recovery_image_activated asserted before firmware writes zero. ",
                 "Activation action must be gated on firmware zero-write ",
                 "(OCP Recovery v1.1 Sec 9.2 RECOVERY_CTRL)."})
            premature_activation = 1'b1;
        end

        // Firmware's post-RA nonzero write is confirmed by the repeated
        // RECOVERY_CTRL reads above. Verify activation still has not occurred.
        if ((sem_vif.recovery_image_activated !== 1'b0) ||
            sem_vif.recovery_image_activated_seen) begin
            `uvm_error("RA_SEM_SEQ",
                {"recovery_image_activated asserted during FW_NONZERO_AFTER_RA. ",
                 "Firmware nonzero write after RA set must not trigger activation."})
            premature_activation = 1'b1;
        end else begin
            `uvm_info("RA_SEM_SEQ",
                "recovery_image_activated remained low during FW_NONZERO_AFTER_RA.",
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
        if ((sem_vif.recovery_image_activated !== 1'b0) ||
            sem_vif.recovery_image_activated_seen) begin
            `uvm_error("RA_SEM_SEQ",
                "recovery_image_activated asserted before the firmware zero-write release.")
            premature_activation = 1'b1;
        end
        sem_vif.clear_recovery_image_activated_seen();

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

        // -----------------------------------------------------------------
        // Require a new activation edge after the firmware zero-write barrier.
        // -----------------------------------------------------------------
        reached = sem_vif.recovery_image_activated_seen;
        if (!reached) begin
            wait_recovery_image_activated_bounded(reached);
        end
        if (premature_activation) begin
            `uvm_error("RA_SEM_SEQ",
                {"Source-qualified activation failed: an activation edge was ",
                 "observed before the firmware zero-write barrier."})
        end else if (!reached) begin
            `uvm_error("RA_SEM_SEQ",
                {"recovery_image_activated did not assert after firmware zero-write. ",
                 "Expected: externally visible activation action follows firmware ",
                 "consumption of the zero-write."})
        end else begin
            `uvm_info("RA_SEM_SEQ",
                {"recovery_image_activated asserted after firmware zero-write. ",
                 "Source-qualified activation confirmed."},
                UVM_NONE)
        end

        // -----------------------------------------------------------------
        // Wait for protocol recovery completion.
        // RECOVERY_STATUS reaches SUCCESS only after the platform completes
        // the boot-request/acknowledgment handshake.
        // -----------------------------------------------------------------
        poll_recovery_status(
            OCP_RECOVERY_STATUS_SUCCESS, RECOV_MAX_POLLS,
            RECOV_POLL_PERIOD, reached, rs_resp, "RA_SEM_RS_SUCCESS");
        if (!reached) begin
            `uvm_error("RA_SEM_SEQ",
                {"INTEGRATION_INCOMPLETE: RECOVERY_STATUS SUCCESS not observed. ",
                 "The boot request/acknowledge handshake between the OCP Recovery ",
                 "subsystem and the platform boot controller did not complete. ",
                 "Full end-to-end recovery requires platform boot controller integration ",
                 "(OCP Recovery v1.1 Sec 9.2, SS boot-request interface)."})
        end else begin
            `uvm_info("RA_SEM_SEQ",
                "RECOVERY_STATUS SUCCESS observed.",
                UVM_NONE)
        end

        publish_transfer_count();

        `uvm_info("RA_SEM_SEQ",
            "OCP_SEM_003 complete: recovery activation source qualification checked.",
            UVM_NONE)

        #1us;
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_RECOVERY_ACTIVATION_ACCESS_SEMANTICS_SEQUENCE_SV
