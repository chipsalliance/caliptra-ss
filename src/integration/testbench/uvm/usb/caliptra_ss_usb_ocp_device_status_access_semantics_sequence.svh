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

`ifndef CALIPTRA_SS_USB_OCP_DEVICE_STATUS_ACCESS_SEMANTICS_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_DEVICE_STATUS_ACCESS_SEMANTICS_SEQUENCE_SV

// =============================================================================
// caliptra_ss_usb_ocp_device_status_access_semantics_sequence
//
// Verifies OCP Recovery v1.1 Sec 9.1 source-qualified clear semantics for
// DEVICE_STATUS PROT_ERROR. CPUif reads are non-destructive; only Recovery
// Agent USB reads perform the protocol-defined clear-on-read.
//
// Choreography:
//  1. Initialize OCP transport and wait for firmware READY state.
//  2. Trigger PROTOCOL_ERROR via legal negative USB write to host-RO
//     PROT_CAP command (1-byte payload).
//  3. Wait firmware CPU_READ_PRESERVED (data = PROT_ERROR code); verify 0x01.
//  4. Perform one USB DEVICE_STATUS read; verify PROT_ERROR=0x01.
//  5. Wait firmware USB_CLEAR_OBSERVED.
//  6. Perform second USB DEVICE_STATUS read; verify PROT_ERROR=0x00.
//  7. Stress loop (4 iterations per firmware):
//     a. Issue negative command.
//     b. Wait firmware STRESS_SET_SEEN (firmware confirmed persistence).
//     c. USB read DEVICE_STATUS; require PROT_ERROR=0x01 (first/clearing read).
//     d. Wait firmware STRESS_CLEAR_SEEN.
//     e. USB read DEVICE_STATUS; require PROT_ERROR=0x00.
//  8. Publish transfer count and summary.
// =============================================================================

class caliptra_ss_usb_ocp_device_status_access_semantics_sequence
    extends caliptra_ss_usb_ocp_recovery_base_sequence;

    `uvm_object_utils(
        caliptra_ss_usb_ocp_device_status_access_semantics_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    // Virtual interface handle obtained from config_db.
    protected virtual caliptra_ss_usb_ocp_access_semantics_if sem_vif;

    // Polling configuration for firmware state waits.
    // max_polls * poll_period bounds the worst-case wall time.
    localparam int unsigned SEM_MAX_POLLS  = 2000;
    localparam time         SEM_POLL_PERIOD = 10us;

    // Number of stress iterations (must match firmware loop count).
    localparam int unsigned STRESS_ITERATIONS = 4;

    function new(string name =
        "caliptra_ss_usb_ocp_device_status_access_semantics_sequence");
        super.new(name);
    endfunction

    // -------------------------------------------------------------------------
    // get_sem_vif: obtain the observation interface from config_db.
    // -------------------------------------------------------------------------
    protected virtual function bit get_sem_vif();
        if (!uvm_config_db#(
                virtual caliptra_ss_usb_ocp_access_semantics_if)::get(
                    null, "uvm_test_top.env",
                    "ocp_access_semantics_if", sem_vif)) begin
            `uvm_fatal("DS_SEM_SEQ",
                "ocp_access_semantics_if not found in config_db under uvm_test_top.env")
            return 1'b0;
        end
        return 1'b1;
    endfunction

    // -------------------------------------------------------------------------
    // wait_fw_state: bounded wait for a specific firmware state code.
    // Emits UVM_ERROR if the state is not observed within the timeout.
    // -------------------------------------------------------------------------
    protected virtual task wait_fw_state(
        input logic [7:0] target_state,
        input string      label);

        bit found;
        sem_vif.wait_for_fw_state_bounded(
            target_state, SEM_MAX_POLLS, SEM_POLL_PERIOD, found);
        if (!found) begin
            `uvm_fatal("DS_SEM_SEQ",
                $sformatf("%s: firmware state 0x%02h not observed within timeout.",
                          label, target_state))
        end
    endtask

    protected virtual task wait_fw_state_data(
        input logic [7:0] target_state,
        input logic [7:0] target_data,
        input string      label);

        bit found;
        sem_vif.wait_for_fw_state_data_bounded(
            target_state, target_data,
            SEM_MAX_POLLS, SEM_POLL_PERIOD, found);
        if (!found) begin
            `uvm_fatal("DS_SEM_SEQ",
                $sformatf("%s: firmware state/data 0x%02h/0x%02h not observed within timeout.",
                          label, target_state, target_data))
        end
    endtask

    // -------------------------------------------------------------------------
    // trigger_protocol_error: issue a legal negative USB write to the
    // host-RO PROT_CAP command (1-byte payload). Per OCP Recovery v1.1
    // Sec 9.1, this causes PROT_ERROR=0x01 (Unsupported Command/Write).
    // -------------------------------------------------------------------------
    protected virtual task trigger_protocol_error(input string label);
        bit [7:0] payload[$];
        caliptra_ss_usb_ocp_xfer_result_e result;

        payload = '{8'h00};
        ocp_try_write(OCP_CMD_PROT_CAP, payload, result, label);
        if (result == OCP_XFER_ABORTED) begin
            `uvm_fatal("DS_SEM_SEQ",
                $sformatf("%s: negative write to PROT_CAP aborted.", label))
        end
        `uvm_info("DS_SEM_SEQ",
            $sformatf("%s: negative write to PROT_CAP completed (%s)",
                      label, result.name()),
            UVM_MEDIUM)
    endtask

    // -------------------------------------------------------------------------
    // read_device_status_prot_error: read DEVICE_STATUS via USB and return
    // the PROT_ERROR byte. Verifies response length. Does NOT check status
    // code legality here since PROT_ERROR presence is the focus.
    // -------------------------------------------------------------------------
    protected virtual task read_device_status_prot_error(
        output logic [7:0] prot_error_out,
        input  string      label);

        bit [7:0] resp[$];
        prot_error_out = 8'h00;
        ocp_read(OCP_CMD_DEVICE_STATUS, resp, label);
        if (resp.size() < (OCP_OFF_DS_PROT_ERROR + 1)) begin
            `uvm_fatal("DS_SEM_SEQ",
                $sformatf("%s: DEVICE_STATUS response too short (%0d bytes).",
                          label, resp.size()))
            return;
        end
        prot_error_out = resp[OCP_OFF_DS_PROT_ERROR];
    endtask

    // -------------------------------------------------------------------------
    // body: main sequence choreography.
    // -------------------------------------------------------------------------
    virtual task body();
        logic [7:0] prot_error_code;
        logic [7:0] observed_error;
        logic [7:0] observed_error2;

        if (!get_sem_vif()) return;

        initialize_ocp_transport();

        // Step 1: Wait for firmware READY.
        wait_fw_state(DS_SEM_STATE_READY, "DS_SEM_READY");
        `uvm_info("DS_SEM_SEQ", "Firmware READY observed.", UVM_NONE)

        // Step 2: Trigger PROTOCOL_ERROR.
        trigger_protocol_error("DS_SEM_NEGATIVE_CMD");

        // Step 3: Wait CPU_READ_PRESERVED; verify data = 0x01.
        wait_fw_state(DS_SEM_STATE_CPU_READ_PRESERVED,
                      "DS_SEM_CPU_READ_PRESERVED");
        prot_error_code = sem_vif.get_fw_data();
        if (prot_error_code !== OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND) begin
            `uvm_error("DS_SEM_SEQ",
                $sformatf("CPU_READ_PRESERVED data=0x%02h expected 0x%02h (UNSUPPORTED_COMMAND).",
                          prot_error_code,
                          OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND))
        end else begin
            `uvm_info("DS_SEM_SEQ",
                $sformatf("CPU_READ_PRESERVED: firmware reports PROT_ERROR=0x%02h (correct).",
                          prot_error_code),
                UVM_NONE)
        end

        // Step 4: USB read DEVICE_STATUS; verify PROT_ERROR=0x01.
        // This is the clearing read per OCP Recovery v1.1 Sec 9.1.
        read_device_status_prot_error(observed_error, "DS_SEM_USB_READ_1");
        if (observed_error !== OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND) begin
            `uvm_error("DS_SEM_SEQ",
                $sformatf("First USB DEVICE_STATUS read PROT_ERROR=0x%02h, expected 0x%02h.",
                          observed_error,
                          OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND))
        end

        // Step 5: Wait firmware USB_CLEAR_OBSERVED.
        wait_fw_state(DS_SEM_STATE_USB_CLEAR_OBSERVED,
                      "DS_SEM_USB_CLEAR_OBSERVED");

        // Step 6: Second USB read; verify PROT_ERROR=0x00.
        read_device_status_prot_error(observed_error2, "DS_SEM_USB_READ_2");
        if (observed_error2 !== OCP_PROTOCOL_ERROR_NONE) begin
            `uvm_error("DS_SEM_SEQ",
                $sformatf("Second USB DEVICE_STATUS read PROT_ERROR=0x%02h, expected 0x00.",
                          observed_error2))
        end else begin
            `uvm_info("DS_SEM_SEQ",
                "Source-qualified clear confirmed: PROT_ERROR=0x00 after RA read.",
                UVM_NONE)
        end

        // Step 7: Stress loop.
        for (int unsigned iter = 1; iter <= STRESS_ITERATIONS; iter++) begin
            // Issue negative command.
            trigger_protocol_error(
                $sformatf("DS_SEM_STRESS_%0d_CMD", iter));

            // Wait firmware SET_SEEN (firmware confirmed PROT_ERROR set and
            // persists across two CPUif reads).
            wait_fw_state_data(
                DS_SEM_STATE_STRESS_SET_SEEN, 8'(iter),
                $sformatf("DS_SEM_STRESS_%0d_SET", iter));

            // First USB read (clearing read); require PROT_ERROR=0x01.
            read_device_status_prot_error(observed_error,
                $sformatf("DS_SEM_STRESS_%0d_USB_READ_1", iter));
            if (observed_error !== OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND) begin
                `uvm_error("DS_SEM_SEQ",
                    $sformatf("Stress iter %0d: first USB read PROT_ERROR=0x%02h, expected 0x%02h.",
                              iter, observed_error,
                              OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND))
            end

            // Wait firmware CLEAR_SEEN.
            wait_fw_state_data(
                DS_SEM_STATE_STRESS_CLEAR_SEEN, 8'(iter),
                $sformatf("DS_SEM_STRESS_%0d_CLEAR", iter));

            // Second USB read; require PROT_ERROR=0x00.
            read_device_status_prot_error(observed_error2,
                $sformatf("DS_SEM_STRESS_%0d_USB_READ_2", iter));
            if (observed_error2 !== OCP_PROTOCOL_ERROR_NONE) begin
                `uvm_error("DS_SEM_SEQ",
                    $sformatf("Stress iter %0d: second USB read PROT_ERROR=0x%02h, expected 0x00.",
                              iter, observed_error2))
            end else begin
                `uvm_info("DS_SEM_SEQ",
                    $sformatf("Stress iter %0d: clear confirmed.", iter),
                    UVM_MEDIUM)
            end
        end

        publish_transfer_count();

        `uvm_info("DS_SEM_SEQ",
            $sformatf("OCP_SEM_001 complete: %0d stress iterations passed; source-qualified clear semantics verified.",
                      STRESS_ITERATIONS),
            UVM_NONE)

        #1us;
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_DEVICE_STATUS_ACCESS_SEMANTICS_SEQUENCE_SV
