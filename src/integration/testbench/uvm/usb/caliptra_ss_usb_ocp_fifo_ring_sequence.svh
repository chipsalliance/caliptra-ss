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

`ifndef CALIPTRA_SS_USB_OCP_FIFO_RING_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_FIFO_RING_SEQUENCE_SV

// OCP Recovery v1.1 Sections 8.2.5 and 9.2 FIFO-ring compliance test.
// Capacity and transfer limits are discovered from INDIRECT_FIFO_STATUS.
class caliptra_ss_usb_ocp_fifo_ring_sequence
    extends caliptra_ss_usb_ocp_recovery_base_sequence;

    typedef struct {
        bit          empty;
        bit          full;
        bit [7:0]    region_type;
        bit [31:0]   write_index;
        bit [31:0]   read_index;
        bit [31:0]   fifo_size;
        bit [31:0]   max_transfer_dwords;
    } fifo_status_s;

    `uvm_object_utils(caliptra_ss_usb_ocp_fifo_ring_sequence)

    function new(string name = "caliptra_ss_usb_ocp_fifo_ring_sequence");
        super.new(name);
    endfunction

    protected virtual function int unsigned ring_occupancy(
        input fifo_status_s status);
        if (status.fifo_size == 0) return 0;
        return (status.write_index + status.fifo_size -
                status.read_index) % status.fifo_size;
    endfunction

    protected virtual function int unsigned ring_space(
        input fifo_status_s status);
        if (status.fifo_size == 0) return 0;
        return (status.read_index + status.fifo_size -
                ((status.write_index + 1) % status.fifo_size)) %
               status.fifo_size;
    endfunction

    protected virtual function int unsigned legal_chunk_dwords(
        input fifo_status_s status);
        int unsigned usb_limit_dwords;

        usb_limit_dwords = wMaxWrTransferSize / 4;
        if (status.max_transfer_dwords < usb_limit_dwords)
            return status.max_transfer_dwords;
        return usb_limit_dwords;
    endfunction

    protected virtual function void append_dword(
        ref bit [7:0] payload[$],
        input bit [31:0] value);
        payload.push_back(value[7:0]);
        payload.push_back(value[15:8]);
        payload.push_back(value[23:16]);
        payload.push_back(value[31:24]);
    endfunction

    protected virtual task read_status(
        output fifo_status_s status,
        input string label);
        bit [7:0] response[$];
        int unsigned occupancy;
        int unsigned space;

        indirect_fifo_status_read(
            response, status.empty, status.full, status.region_type,
            status.write_index, status.read_index, status.fifo_size,
            status.max_transfer_dwords, label);

        if ((status.fifo_size < 2) || (status.fifo_size > 4096)) begin
            `uvm_fatal("OCP_FIFO_RING",
                $sformatf("%s reported FIFO_SIZE=%0d; expected a usable ring in range 2..4096.",
                          label, status.fifo_size))
        end
        if (status.max_transfer_dwords == 0) begin
            `uvm_fatal("OCP_FIFO_RING",
                $sformatf("%s reported MAX_TRANSFER_SIZE=0.", label))
        end
        if ((status.write_index >= status.fifo_size) ||
            (status.read_index >= status.fifo_size)) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("%s index out of range: WRITE_INDEX=%0d READ_INDEX=%0d FIFO_SIZE=%0d.",
                          label, status.write_index, status.read_index,
                          status.fifo_size))
            return;
        end
        if (status.region_type != OCP_REGION_RECOVERY_CODE_WO) begin
            `uvm_fatal("OCP_FIFO_RING",
                $sformatf("%s REGION_TYPE=0x%02h; expected recovery code write-only region 0x%02h.",
                          label, status.region_type,
                          OCP_REGION_RECOVERY_CODE_WO))
        end

        occupancy = ring_occupancy(status);
        space = ring_space(status);
        if (status.empty !== (occupancy == 0)) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("%s EMPTY=%0b conflicts with occupancy=%0d.",
                          label, status.empty, occupancy))
        end
        if (status.full !== (space == 0)) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("%s FULL=%0b conflicts with available space=%0d.",
                          label, status.full, space))
        end
    endtask

    protected virtual task read_data_and_check(
        input bit [31:0] expected,
        input string label);
        bit [7:0] response[$];
        bit [31:0] observed;

        ocp_read(OCP_CMD_INDIRECT_FIFO_DATA, response, label);
        if (response.size() != 4) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("%s returned %0d bytes; expected one DWORD.",
                          label, response.size()))
            return;
        end
        observed = get_le32(response, 0);
        if (observed !== expected) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("%s data mismatch: expected 0x%08h got 0x%08h.",
                          label, expected, observed))
        end
    endtask

    virtual task body();
        fifo_status_s status;
        fifo_status_s initial_status;
        fifo_status_s full_status;
        fifo_status_s rejected_status;
        bit [31:0] payload_dwords[$];
        bit [7:0] payload[$];
        bit [31:0] wrap_dword;
        caliptra_ss_usb_ocp_xfer_result_e extra_result;
        int unsigned usable_capacity;
        int unsigned max_chunk;
        int unsigned offset;
        int unsigned chunk;
        int unsigned base_index;
        bit slot_visible;

        initialize_ocp_transport();
        recovery_ctrl_write(
            8'h00, 8'h00, 1'b0, "OCP_FIFO_RING_RECOVERY_CTRL");

        read_status(initial_status, "OCP_FIFO_RING_CAPABILITY_STATUS");
        usable_capacity = initial_status.fifo_size - 1;
        max_chunk = legal_chunk_dwords(initial_status);
        if (max_chunk == 0) begin
            `uvm_fatal("OCP_FIFO_RING",
                "Runtime FIFO and USB transfer limits do not permit one DWORD.")
        end

        // The sequence performs usable_capacity initial writes plus one refill.
        indirect_fifo_ctrl_write(
            8'h00, 1'b1, initial_status.fifo_size,
            "OCP_FIFO_RING_CTRL");
        read_status(status, "OCP_FIFO_RING_STATUS_RESET");
        if (!status.empty || status.full ||
            (status.write_index != status.read_index)) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("Reset state invalid: EMPTY=%0b FULL=%0b WRITE_INDEX=%0d READ_INDEX=%0d.",
                          status.empty, status.full,
                          status.write_index, status.read_index))
        end
        if ((status.fifo_size != initial_status.fifo_size) ||
            (status.max_transfer_dwords !=
                initial_status.max_transfer_dwords)) begin
            `uvm_error("OCP_FIFO_RING",
                "FIFO capabilities changed across reset.")
        end
        base_index = status.write_index;

        payload_dwords.delete();
        for (int unsigned i = 0; i < usable_capacity; i++) begin
            payload_dwords.push_back(32'hA5A5_0000 ^ i);
        end

        offset = 0;
        chunk = 0;
        while (offset < usable_capacity) begin
            int unsigned chunk_dwords;
            chunk_dwords = usable_capacity - offset;
            if (chunk_dwords > max_chunk) chunk_dwords = max_chunk;
            payload.delete();
            for (int unsigned i = 0; i < chunk_dwords; i++) begin
                append_dword(payload, payload_dwords[offset + i]);
            end
            indirect_fifo_data_write(
                payload, $sformatf("OCP_FIFO_RING_PUSH_%0d", chunk));
            offset += chunk_dwords;
            chunk++;
        end

        read_status(full_status, "OCP_FIFO_RING_STATUS_FULL");
        if (!full_status.full || full_status.empty ||
            (ring_occupancy(full_status) != usable_capacity) ||
            (full_status.write_index !=
                ((base_index + usable_capacity) %
                    full_status.fifo_size))) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("Full state invalid: EMPTY=%0b FULL=%0b WRITE_INDEX=%0d READ_INDEX=%0d occupancy=%0d expected_occupancy=%0d.",
                          full_status.empty, full_status.full,
                          full_status.write_index, full_status.read_index,
                          ring_occupancy(full_status), usable_capacity))
        end

        wrap_dword = 32'hFACE_CAFE;
        payload.delete();
        append_dword(payload, wrap_dword);
        indirect_fifo_data_try_write(
            payload, extra_result, "OCP_FIFO_RING_REJECTED_PUSH");
        read_status(rejected_status, "OCP_FIFO_RING_STATUS_REJECTED_PUSH");
        if ((rejected_status.write_index != full_status.write_index) ||
            (rejected_status.read_index != full_status.read_index) ||
            (ring_occupancy(rejected_status) !=
                ring_occupancy(full_status))) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("Overrun attempt changed ring state: before W=%0d R=%0d occ=%0d after W=%0d R=%0d occ=%0d result=%s.",
                          full_status.write_index, full_status.read_index,
                          ring_occupancy(full_status),
                          rejected_status.write_index,
                          rejected_status.read_index,
                          ring_occupancy(rejected_status),
                          extra_result.name()))
        end

        read_data_and_check(
            payload_dwords[0], "OCP_FIFO_RING_POP_0");

        slot_visible = 1'b0;
        for (int unsigned poll = 0; poll < 16; poll++) begin
            read_status(
                status, $sformatf("OCP_FIFO_RING_STATUS_POLL_%0d", poll));
            if (status.write_index != full_status.write_index) begin
                `uvm_error("OCP_FIFO_RING",
                    $sformatf("Post-pop status changed WRITE_INDEX from %0d to %0d before refill.",
                              full_status.write_index,
                              status.write_index))
            end
            if (ring_space(status) != 0) begin
                slot_visible = 1'b1;
                break;
            end
            #1us;
        end
        if (!slot_visible) begin
            `uvm_fatal("OCP_FIFO_RING",
                "No protocol-visible FIFO space appeared after one DWORD was read.")
        end

        payload.delete();
        append_dword(payload, wrap_dword);
        indirect_fifo_data_write(
            payload, "OCP_FIFO_RING_WRAP_PUSH_ACCEPTED");
        read_status(status, "OCP_FIFO_RING_STATUS_AFTER_REFILL");
        if (!status.full ||
            (status.write_index !=
                ((full_status.write_index + 1) % status.fifo_size)) ||
            (ring_occupancy(status) != usable_capacity)) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("Refill state invalid: FULL=%0b WRITE_INDEX=%0d expected=%0d occupancy=%0d.",
                          status.full, status.write_index,
                          (full_status.write_index + 1) % status.fifo_size,
                          ring_occupancy(status)))
        end

        for (int unsigned i = 1; i < payload_dwords.size(); i++) begin
            read_data_and_check(
                payload_dwords[i],
                $sformatf("OCP_FIFO_RING_POP_%0d", i));
        end
        read_data_and_check(
            wrap_dword, "OCP_FIFO_RING_POP_WRAP_WORD");

        read_status(status, "OCP_FIFO_RING_STATUS_EMPTY");
        if (!status.empty || status.full ||
            (status.write_index != status.read_index) ||
            (ring_occupancy(status) != 0)) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("Final empty state invalid: EMPTY=%0b FULL=%0b WRITE_INDEX=%0d READ_INDEX=%0d occupancy=%0d.",
                          status.empty, status.full,
                          status.write_index, status.read_index,
                          ring_occupancy(status)))
        end

        publish_transfer_count();
        `uvm_info("OCP_FIFO_RING",
            $sformatf("FIFO ring test complete: FIFO_SIZE=%0d usable=%0d MAX_TRANSFER_SIZE=%0d USB_MAX_WR_BYTES=%0d.",
                      status.fifo_size, usable_capacity,
                      status.max_transfer_dwords,
                      wMaxWrTransferSize),
            UVM_NONE)
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_FIFO_RING_SEQUENCE_SV
