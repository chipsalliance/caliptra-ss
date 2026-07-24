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
//
// Test intent:
//   1. Discover FIFO_SIZE and transfer limits at runtime from INDIRECT_FIFO_STATUS.
//   2. Reset the ring and fill FIFO_SIZE-1 slots with deterministic DWORDs.
//   3. While the FIFO is full, attempt one additional write and prove the
//      Device issues a packet-level USB NAK and the ring state is unchanged.
//   4. Poll for firmware to pop the first DWORD (READ_INDEX advances by 1).
//   5. Push the final DWORD causing WRITE_INDEX to wrap modulo FIFO_SIZE.
//   6. Poll for firmware to drain all remaining DWORDs and FIFO to be EMPTY.
//
// OCP Recovery v1.1 Sec 9.2 defines region type 0b000 as write-only from
// the Recovery Agent; the RA must never issue an IN transfer on
// INDIRECT_FIFO_DATA for this region.  All Device consumption is tracked
// through READ_INDEX polling on INDIRECT_FIFO_STATUS.
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

    // Upper bounds for Device state-transition polls.
    // Values are chosen to accommodate simulation latency without coupling to
    // any specific RTL depth or clock ratio.
    localparam int unsigned OCP_FIFO_RING_MAX_POP_POLLS   = 512;
    localparam int unsigned OCP_FIFO_RING_MAX_EMPTY_POLLS = 256;

    // NAK monitor callback registered against the link monitor to detect
    // packet-level backpressure per OCP Recovery v1.1 Sec 8.2.5.
    protected caliptra_ss_usb_nak_monitor_callback nak_cb;

    function new(string name = "caliptra_ss_usb_ocp_fifo_ring_sequence");
        super.new(name);
    endfunction

    // Occupancy formula from OCP Recovery v1.1 Sec 8.2.5.
    protected virtual function int unsigned ring_occupancy(
        input fifo_status_s status);
        if (status.fifo_size == 0) return 0;
        return (status.write_index + status.fifo_size -
                status.read_index) % status.fifo_size;
    endfunction

    // Available space formula from OCP Recovery v1.1 Sec 8.2.5.
    // Space is 0 when WRITE_INDEX+1 mod FIFO_SIZE would equal READ_INDEX (FULL).
    protected virtual function int unsigned ring_space(
        input fifo_status_s status);
        if (status.fifo_size == 0) return 0;
        return (status.read_index + status.fifo_size -
                ((status.write_index + 1) % status.fifo_size)) %
               status.fifo_size;
    endfunction

    // Smallest legal write chunk in DWORDs: min of OCP MAX_TRANSFER_SIZE
    // and the USB functional descriptor wMaxWrTransferSize.
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

    // Read INDIRECT_FIFO_STATUS and validate structural invariants.
    // FIFO_SIZE is runtime-discovered per OCP Recovery v1.1 Sec 8.2.5;
    // no implementation-derived upper bound is imposed beyond requiring
    // a functional ring (>= 2 slots) and a non-zero transfer limit.
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

        if (status.fifo_size < 2) begin
            `uvm_fatal("OCP_FIFO_RING",
                $sformatf("%s reported FIFO_SIZE=%0d; ring requires at least 2 slots per OCP Recovery v1.1 Sec 8.2.5.",
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
        // Region type 0b000 is recovery code write-only per OCP Recovery
        // v1.1 Sec 9.2.  The RA must not issue IN transfers on INDIRECT_FIFO_DATA.
        if (status.region_type !== OCP_REGION_RECOVERY_CODE_WO) begin
            `uvm_fatal("OCP_FIFO_RING",
                $sformatf("%s REGION_TYPE=0x%02h; expected recovery code write-only region 0x%02h per OCP Recovery v1.1 Sec 9.2.",
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

    virtual task body();
        fifo_status_s status;
        fifo_status_s initial_status;
        fifo_status_s full_status;
        fifo_status_s rejected_status;
        bit [7:0]    payload[$];
        bit [31:0]   wrap_dword;
        caliptra_ss_usb_ocp_xfer_result_e extra_result;
        int unsigned usable_capacity;
        int unsigned max_chunk;
        int unsigned offset;
        int unsigned chunk;
        int unsigned base_index;
        int unsigned nak_before_overflow;
        int unsigned nak_after_overflow;
        int unsigned expected_read_after_pop;
        bit pop_visible;
        bit empty_reached;

        initialize_ocp_transport();
        recovery_ctrl_write(
            8'h00, 8'h00, 1'b0, "OCP_FIFO_RING_RECOVERY_CTRL");

        // Register the USB NAK monitor callback and reset the packet counter.
        // The same registration pattern is used by the shared
        // caliptra_ss_usb_ocp_fifo_flow_control_sequence USB-NAK strategy so
        // the callback infrastructure is exercised consistently across tests.
        nak_cb = caliptra_ss_usb_nak_monitor_callback::type_id::create(
            "nak_cb");
        uvm_callbacks#(
            svt_usb_link_monitor,
            svt_usb_link_monitor_callback)::add(
                host_agent_h.link_mon, nak_cb);
        caliptra_ss_usb_nak_monitor_callback::reset_nak_count();

        // Capability discovery: FIFO_SIZE and limits are runtime fields per
        // OCP Recovery v1.1 Sec 8.2.5.  No compile-time values are assumed.
        read_status(initial_status, "OCP_FIFO_RING_CAPABILITY_STATUS");
        usable_capacity = initial_status.fifo_size - 1;
        max_chunk = legal_chunk_dwords(initial_status);
        if (max_chunk == 0) begin
            `uvm_fatal("OCP_FIFO_RING",
                "Runtime FIFO and USB transfer limits do not permit one DWORD.")
        end

        // Program IMAGE_SIZE = FIFO_SIZE in INDIRECT_FIFO_CTRL so firmware
        // can read the total expected consumption count from that register.
        // Reset the ring to guarantee clean EMPTY state before filling.
        indirect_fifo_ctrl_write(
            8'h00, 1'b1, initial_status.fifo_size,
            "OCP_FIFO_RING_CTRL");
        read_status(status, "OCP_FIFO_RING_STATUS_RESET");
        if (!status.empty || status.full ||
            (status.write_index !== status.read_index)) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("Reset state invalid: EMPTY=%0b FULL=%0b WRITE_INDEX=%0d READ_INDEX=%0d.",
                          status.empty, status.full,
                          status.write_index, status.read_index))
        end
        if ((status.fifo_size !== initial_status.fifo_size) ||
            (status.max_transfer_dwords !==
                initial_status.max_transfer_dwords)) begin
            `uvm_error("OCP_FIFO_RING",
                "FIFO capabilities changed across reset.")
        end
        base_index = status.write_index;

        // Initial fill: push FIFO_SIZE-1 DWORDs with deterministic pattern
        // 32'hC0DE_0000 | word_index for word_index 0..FIFO_SIZE-2.
        // This leaves exactly one free slot, making the FIFO full.
        offset = 0;
        chunk  = 0;
        while (offset < usable_capacity) begin
            int unsigned chunk_dwords;
            chunk_dwords = usable_capacity - offset;
            if (chunk_dwords > max_chunk) chunk_dwords = max_chunk;
            payload.delete();
            for (int unsigned i = 0; i < chunk_dwords; i++) begin
                append_dword(payload, 32'hC0DE_0000 | (32'(offset + i)));
            end
            indirect_fifo_data_write(
                payload, $sformatf("OCP_FIFO_RING_PUSH_%0d", chunk));
            offset += chunk_dwords;
            chunk++;
        end

        read_status(full_status, "OCP_FIFO_RING_STATUS_FULL");
        if (!full_status.full || full_status.empty ||
            (ring_occupancy(full_status) !== usable_capacity) ||
            (full_status.write_index !==
                ((base_index + usable_capacity) %
                    full_status.fifo_size))) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("Full state invalid: EMPTY=%0b FULL=%0b WRITE_INDEX=%0d READ_INDEX=%0d occupancy=%0d expected_occupancy=%0d.",
                          full_status.empty, full_status.full,
                          full_status.write_index, full_status.read_index,
                          ring_occupancy(full_status), usable_capacity))
        end

        // Overflow write: FIFO is full; per OCP Recovery v1.1 Sec 8.2.5 the
        // Device shall NACK a transfer that would advance WRITE_INDEX to
        // READ_INDEX.  Bracket the attempt with NAK counts to confirm the
        // rejection is a packet-level USB NAK, not a STALL or abort.
        // wrap_dword uses the deterministic pattern at index FIFO_SIZE-1.
        wrap_dword = 32'hC0DE_0000 | (32'(usable_capacity));
        payload.delete();
        append_dword(payload, wrap_dword);

        nak_before_overflow =
            caliptra_ss_usb_nak_monitor_callback::get_nak_count();
        indirect_fifo_data_try_write(
            payload, extra_result, "OCP_FIFO_RING_OVERFLOW_PUSH");
        nak_after_overflow =
            caliptra_ss_usb_nak_monitor_callback::get_nak_count();

        // Per OCP Recovery v1.1 Sec 8.2.5 an overflow write must be rejected.
        if (extra_result === OCP_XFER_SUCCESS) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("Overflow write on full FIFO succeeded (result=%s); Device shall reject per OCP Recovery v1.1 Sec 8.2.5.",
                          extra_result.name()))
        end
        // A packet-level USB NAK must be observed. The completed VIP transfer
        // may subsequently report a timeout after repeated NAK responses.
        if (nak_after_overflow <= nak_before_overflow) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("No USB NAK observed for overflow attempt (nak_before=%0d nak_after=%0d); OCP Recovery v1.1 Sec 8.2.5 requires packet-level NACK.",
                          nak_before_overflow, nak_after_overflow))
        end

        // Verify the rejected write did not change ring state per
        // OCP Recovery v1.1 Sec 8.2.5 (space and occupancy modulo formulas).
        read_status(rejected_status, "OCP_FIFO_RING_STATUS_REJECTED_PUSH");
        if ((rejected_status.write_index !== full_status.write_index) ||
            (rejected_status.read_index  !== full_status.read_index)  ||
            (ring_occupancy(rejected_status) !==
                ring_occupancy(full_status))) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("Rejected overflow changed ring state: before W=%0d R=%0d occ=%0d after W=%0d R=%0d occ=%0d result=%s.",
                          full_status.write_index, full_status.read_index,
                          ring_occupancy(full_status),
                          rejected_status.write_index,
                          rejected_status.read_index,
                          ring_occupancy(rejected_status),
                          extra_result.name()))
        end

        // Poll for Device READ_INDEX to advance by exactly one slot.
        // Per OCP Recovery v1.1 Sec 9.2 READ_INDEX advances when the Device
        // consumes a DWORD from the ring.  The firmware pops word 0 (0xC0DE_0000)
        // after observing FULL and expiring the configured hold delay.
        expected_read_after_pop =
            (full_status.read_index + 1) % full_status.fifo_size;
        pop_visible = 1'b0;
        for (int unsigned poll = 0;
             poll < OCP_FIFO_RING_MAX_POP_POLLS; poll++) begin
            read_status(
                status,
                $sformatf("OCP_FIFO_RING_POP_POLL_%0d", poll));
            // WRITE_INDEX must not change before the refill write below.
            if (status.write_index !== full_status.write_index) begin
                `uvm_error("OCP_FIFO_RING",
                    $sformatf("WRITE_INDEX changed unexpectedly during pop-poll %0d: was %0d now %0d.",
                              poll, full_status.write_index,
                              status.write_index))
            end
            if (status.read_index === expected_read_after_pop) begin
                pop_visible = 1'b1;
                break;
            end
            #1us;
        end
        if (!pop_visible) begin
            `uvm_fatal("OCP_FIFO_RING",
                $sformatf("Device READ_INDEX did not advance from %0d to %0d within %0d polls.",
                          full_status.read_index, expected_read_after_pop,
                          OCP_FIFO_RING_MAX_POP_POLLS))
        end

        // Refill: push wrap_dword (word_index = FIFO_SIZE-1, pattern C0DE_0000|(FIFO_SIZE-1)).
        // One free slot exists after the firmware pop, so this write must succeed.
        // WRITE_INDEX wraps modulo FIFO_SIZE: (full_status.write_index+1) % FIFO_SIZE.
        payload.delete();
        append_dword(payload, wrap_dword);
        indirect_fifo_data_write(
            payload, "OCP_FIFO_RING_WRAP_PUSH_ACCEPTED");

        read_status(status, "OCP_FIFO_RING_STATUS_AFTER_REFILL");
        if (status.write_index !==
                ((full_status.write_index + 1) % status.fifo_size)) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("Refill WRITE_INDEX=%0d, expected modulo rollover to %0d.",
                          status.write_index,
                          (full_status.write_index + 1) %
                              status.fifo_size))
        end

        // Poll for Device to drain all remaining DWORDs and signal EMPTY.
        // EMPTY is set when READ_INDEX == WRITE_INDEX per OCP Recovery v1.1
        // Sec 8.2.5.  Firmware validates all FIFO_SIZE words in order before
        // asserting the completion signal.
        empty_reached = 1'b0;
        for (int unsigned poll = 0;
             poll < OCP_FIFO_RING_MAX_EMPTY_POLLS; poll++) begin
            read_status(
                status,
                $sformatf("OCP_FIFO_RING_EMPTY_POLL_%0d", poll));
            if (status.empty &&
                (status.write_index === status.read_index) &&
                (ring_occupancy(status) === 0)) begin
                empty_reached = 1'b1;
                break;
            end
            #1us;
        end
        if (!empty_reached) begin
            `uvm_fatal("OCP_FIFO_RING",
                $sformatf("FIFO did not reach EMPTY within %0d polls after firmware drain.",
                          OCP_FIFO_RING_MAX_EMPTY_POLLS))
        end
        if (!status.empty || status.full ||
            (status.write_index !== status.read_index) ||
            (ring_occupancy(status) !== 0)) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("Final empty state invalid: EMPTY=%0b FULL=%0b WRITE_INDEX=%0d READ_INDEX=%0d occupancy=%0d.",
                          status.empty, status.full,
                          status.write_index, status.read_index,
                          ring_occupancy(status)))
        end

        // Publish the expected Device consumption count so the scoreboard can
        // optionally validate that exactly FIFO_SIZE DWORDs were read by firmware.
        uvm_config_db#(int unsigned)::set(
            null, "*", "ocp_expected_fifo_external_reads",
            initial_status.fifo_size);
        publish_transfer_count();

        `uvm_info("OCP_FIFO_RING",
            $sformatf("FIFO ring test complete: FIFO_SIZE=%0d usable=%0d MAX_TRANSFER_SIZE=%0d USB_MAX_WR_BYTES=%0d overflow_naks=%0d transfers=%0d.",
                      status.fifo_size, usable_capacity,
                      status.max_transfer_dwords,
                      wMaxWrTransferSize,
                      nak_after_overflow - nak_before_overflow,
                      transfers_issued),
            UVM_NONE)
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_FIFO_RING_SEQUENCE_SV
