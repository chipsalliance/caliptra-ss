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

`ifndef CALIPTRA_SS_USB_OCP_FIFO_BOUNDARIES_SEQUENCE_SVH
`define CALIPTRA_SS_USB_OCP_FIFO_BOUNDARIES_SEQUENCE_SVH

class caliptra_ss_usb_ocp_fifo_boundaries_sequence
    extends caliptra_ss_usb_ocp_fifo_flow_control_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_fifo_boundaries_sequence)

    localparam time FW_TIMEOUT = 20ms;
    localparam time PUBLICATION_BOUND = 200us;
    localparam int unsigned BOUNDARY_BYTES = 256;
    protected fifo_status_s capabilities;
    protected logic [15:0] generation;

    function new(string name = "caliptra_ss_usb_ocp_fifo_boundaries_sequence");
        super.new(name);
        generation = 0;
    endfunction

    protected task wait_publication(input bit expected, input string label);
        bit observed;
        observed = 1'b0;
        fork : bounded_publication
            begin
                wait (sem_vif.recovery_payload_available === expected);
                observed = 1'b1;
            end
            begin
                #(PUBLICATION_BOUND);
            end
        join_any
        disable bounded_publication;
        if (!observed)
            `uvm_fatal("OCP_FIFO_BOUNDARIES",
                $sformatf("%s payload_available did not reach %0b within the test service bound.",
                          label, expected))
    endtask

    protected task check_indices(
        input int unsigned sent,
        input int unsigned drained,
        input string label);
        fifo_status_s status;
        ocp_fifo_do_read_and_check_status(status, label);
        // This campaign checks the project's full-capacity service-window
        // contract, also exercised by the existing FIFO ring test.
        if ((status.write_index != (sent % capabilities.fifo_size)) ||
            (status.read_index != (drained % capabilities.fifo_size)) ||
            (status.empty != (sent == drained)) ||
            (status.full != ((sent - drained) == capabilities.fifo_size))) begin
            `uvm_fatal("OCP_FIFO_BOUNDARIES",
                $sformatf("%s sent=%0d drained=%0d W=%0d R=%0d EMPTY=%0b FULL=%0b.",
                          label, sent, drained, status.write_index,
                          status.read_index, status.empty, status.full))
        end
    endtask

    protected task push_window(
        input int unsigned case_id,
        input int unsigned start_dword,
        input int unsigned end_dword,
        input int unsigned chunk_limit,
        input int unsigned drained,
        ref int unsigned chunks);
        int unsigned offset;
        int unsigned count;
        bit published;
        bit [7:0] payload[$];
        caliptra_ss_usb_ocp_xfer_result_e result;

        offset = start_dword;
        while (offset < end_dword) begin
            count = end_dword - offset;
            if (count > chunk_limit) count = chunk_limit;
            ocp_fifo_prepare_payload_slice(offset, count, payload);
            if ((case_id == 4) &&
                (payload.size() != wMaxWrTransferSize))
                `uvm_fatal("OCP_FIFO_BOUNDARIES",
                    "FIFO_004 transfer is not exactly wMaxWrTransferSize.")
            if ((case_id == 3) && ((offset + count) == image_dwords) &&
                ((payload.size() % 4) != 3))
                `uvm_fatal("OCP_FIFO_BOUNDARIES",
                    "FIFO_003 terminal transfer must contain three valid bytes in its last DWORD.")
            ocp_do_fifo_data_write(payload, result,
                $sformatf("FIFO_%03d_DATA_%0d", case_id, chunks), 0);
            if (result != OCP_XFER_SUCCESS)
                `uvm_fatal("OCP_FIFO_BOUNDARIES",
                    $sformatf("FIFO_%03d chunk %0d returned %s.",
                              case_id, chunks, result.name()))
            offset += count;
            chunks++;
            check_indices(offset, drained,
                $sformatf("FIFO_%03d_AFTER_%0d_DWORDS", case_id, offset));
            published = ((offset - drained) == capabilities.fifo_size) ||
                        (offset == image_dwords);
            if (!published &&
                ((sem_vif.recovery_payload_available !== 1'b0) ||
                 sem_vif.recovery_payload_available_seen))
                `uvm_fatal("OCP_FIFO_BOUNDARIES",
                    $sformatf("FIFO_%03d published prematurely at %0d DWORDs.",
                              case_id, offset))
            wait_publication(published, $sformatf("FIFO_%03d", case_id));
            `uvm_info("OCP_FIFO_BOUNDARIES",
                $sformatf("FIFO_%03d accepted bytes=%0d cumulative_dwords=%0d payload_available=%0b.",
                          case_id, payload.size(), offset, published),
                UVM_NONE)
        end
    endtask

    protected task drain_window(input bit final_window, input string label);
        generation++;
        ocp_issue_fw_command_and_wait(
            sem_vif.FW_COMMAND_FLOW_ADVANCE, generation,
            final_window ? OCP_FW_STATE_RECOVERY_PENDING :
                           sem_vif.FW_STATE_PATH_READY,
            FW_TIMEOUT, label, "OCP_FIFO_BOUNDARIES");
        wait_publication(1'b0, label);
        sem_vif.clear_recovery_payload_available_seen();
    endtask

    virtual task body();
        int unsigned chunk_limit;
        int unsigned chunks;
        int unsigned first_window;

        if (!ocp_configure_sem_vif())
            `uvm_fatal("OCP_FIFO_BOUNDARIES", "Missing recovery semantics interface.")
        ocp_do_initialize_and_check_transport();
        ocp_wait_fw_state_generation(
            sem_vif.FW_STATE_PATH_READY, 16'h0000, FW_TIMEOUT,
            "FIFO_BOUNDARIES_READY", "OCP_FIFO_BOUNDARIES");
        ocp_fifo_do_read_and_check_status(capabilities, "FIFO_BOUNDARIES_DISCOVERY");
        chunk_limit = ocp_get_max_chunk_dwords(capabilities);
        if ((capabilities.region_type != OCP_REGION_RECOVERY_CODE_WO) ||
            (capabilities.fifo_size * 4 != BOUNDARY_BYTES) ||
            (wMaxWrTransferSize < 64) || ((wMaxWrTransferSize % 4) != 0) ||
            (chunk_limit != (wMaxWrTransferSize / 4)) ||
            ((2 * chunk_limit) > capabilities.fifo_size))
            `uvm_fatal("OCP_FIFO_BOUNDARIES",
                $sformatf({"Campaign requires a 256-byte FIFO and room for two ",
                           "advertised maximum writes: FIFO_SIZE=%0d ",
                           "MAX_TRANSFER_SIZE=%0d wMaxWrTransferSize=%0d."},
                          capabilities.fifo_size,
                          capabilities.max_transfer_dwords, wMaxWrTransferSize))

        for (int unsigned case_id = 1; case_id <= 5; case_id++) begin
            image_bytes.delete();
            final_valid_bytes = (case_id == 3) ? 3 : 4;
            case (case_id)
                1: image_dwords = 12;
                2: image_dwords = 1;
                3: image_dwords = chunk_limit + 1;
                4: image_dwords = 2 * chunk_limit;
                5: image_dwords = (BOUNDARY_BYTES / 4) + 1;
            endcase
            ocp_fifo_prepare_default_image();
            ocp_do_fifo_image_config_xfers(
                cms, OCP_RC_IMAGE_SEL_CMS, image_dwords,
                $sformatf("FIFO_%03d_SELECT", case_id),
                $sformatf("FIFO_%03d_CONFIG", case_id));
            check_indices(0, 0, $sformatf("FIFO_%03d_RESET", case_id));
            wait_publication(1'b0, "FIFO_RESET");
            sem_vif.clear_recovery_payload_available_seen();
            chunks = 0;
            first_window = image_dwords;
            if (first_window > capabilities.fifo_size)
                first_window = capabilities.fifo_size;
            push_window(case_id, 0, first_window,
                (case_id == 1) ? image_dwords : chunk_limit, 0, chunks);
            drain_window(first_window == image_dwords,
                $sformatf("FIFO_%03d_FIRST_DRAIN", case_id));
            check_indices(first_window, first_window, "FIFO_FIRST_WINDOW_EMPTY");
            if (first_window < image_dwords) begin
                push_window(case_id, first_window, image_dwords,
                    chunk_limit, first_window, chunks);
                drain_window(1'b1, "FIFO_005_SECOND_DRAIN");
            end
            check_indices(image_dwords, image_dwords,
                $sformatf("FIFO_%03d_FINAL_EMPTY", case_id));
            ocp_do_poll_and_check_recovery_status_pair(
                OCP_DEVICE_STATUS_RECOVERY_PENDING,
                OCP_RECOVERY_STATUS_AWAITING_IMAGE,
                4'h0, 8'h00, OCP_PROTOCOL_ERROR_NONE,
                200, 1us, $sformatf("FIFO_%03d_PENDING", case_id),
                "OCP_FIFO_BOUNDARIES");
            `uvm_info("OCP_FIFO_BOUNDARIES",
                $sformatf("OCP_FIFO_%03d_PASS bytes=%0d dwords=%0d chunks=%0d: indices, publication, firmware content and RECOVERY_PENDING verified.",
                          case_id, image_bytes.size(), image_dwords, chunks),
                UVM_NONE)
            generation++;
            ocp_issue_fw_command_and_wait(
                sem_vif.FW_COMMAND_FLOW_COMPLETE, generation,
                (case_id == 5) ? sem_vif.FW_STATE_FLOW_COMPLETE :
                                 sem_vif.FW_STATE_PATH_READY,
                FW_TIMEOUT, "FIFO_CASE_COMPLETE", "OCP_FIFO_BOUNDARIES");
        end
        ocp_poll_mcu_axi_idle("OCP_FIFO_BOUNDARIES");
        ocp_publish_transfer_count();
    endtask

endclass

`endif
