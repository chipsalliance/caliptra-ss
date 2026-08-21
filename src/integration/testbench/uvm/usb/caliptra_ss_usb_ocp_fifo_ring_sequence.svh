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
//   2. Reset the FIFO and fill FIFO_SIZE DWORDs with deterministic data.
//   3. Report a compliance failure if the equality-crossing transfer is
//      accepted; OCP Recovery v1.1 Sec 8.2.5 requires NACK before W == R.
//   4. Start one additional DATA transfer and allow the VIP to retry its DATA
//      stage after NAK without issuing another SETUP.
//   5. Require the retry to ACK after Caliptra drains the first batch, then
//      poll the terminal one-DWORD batch to EMPTY.
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
    localparam int unsigned OCP_FIFO_RING_MAX_EMPTY_POLLS = 256;

    // NAK monitor callback registered against the link monitor to detect
    // packet-level backpressure per OCP Recovery v1.1 Sec 8.2.5.
    protected caliptra_ss_usb_nak_monitor_callback nak_cb;

    function new(string name = "caliptra_ss_usb_ocp_fifo_ring_sequence");
        super.new(name);
    endfunction

    protected virtual function int unsigned visible_occupancy(
        input fifo_status_s status);
        if (status.empty && status.full) return 0;
        if (status.empty) return 0;
        if (status.full) return status.fifo_size;
        if (status.fifo_size == 0) return 0;
        return (status.write_index + status.fifo_size -
                status.read_index) % status.fifo_size;
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

        if (status.empty && status.full) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("%s reports EMPTY and FULL simultaneously.", label))
        end
    endtask

    virtual task body();
        fifo_status_s status;
        fifo_status_s initial_status;
        fifo_status_s full_status;
        bit [7:0]    payload[$];
        caliptra_ss_usb_ocp_xfer_result_e extra_result;
        int unsigned max_chunk;
        int unsigned offset;
        int unsigned chunk;
        int unsigned base_index;
        int unsigned nak_before_overflow;
        int unsigned nak_after_overflow;
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
        max_chunk = legal_chunk_dwords(initial_status);
        if (max_chunk == 0) begin
            `uvm_fatal("OCP_FIFO_RING",
                "Runtime FIFO and USB transfer limits do not permit one DWORD.")
        end

        // The terminal retry contributes one DWORD after the first batch.
        indirect_fifo_ctrl_write(
            8'h00, 1'b1, initial_status.fifo_size + 1,
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

        // Fill one implementation-sized batch using only runtime-discovered
        // limits. The final accepted chunk advances W equal to R on the merged
        // design, which is recorded below as an OCP Sec 8.2.5 deviation.
        offset = 0;
        chunk  = 0;
        while (offset < initial_status.fifo_size) begin
            int unsigned chunk_dwords;
            chunk_dwords = initial_status.fifo_size - offset;
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
            (visible_occupancy(full_status) !== full_status.fifo_size) ||
            (full_status.write_index !== full_status.read_index) ||
            (full_status.write_index !== base_index)) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("Merged full-batch state invalid: EMPTY=%0b FULL=%0b WRITE_INDEX=%0d READ_INDEX=%0d occupancy=%0d.",
                          full_status.empty, full_status.full,
                          full_status.write_index, full_status.read_index,
                          visible_occupancy(full_status)))
        end
        `uvm_error("OCP_FIFO_RING",
            "Device accepted the equality-crossing FIFO transfer and reported FULL with WRITE_INDEX == READ_INDEX; OCP Recovery v1.1 Sec 8.2.5 requires NACK.")

        // Keep one CONTROL OUT transfer active. The VIP retries the same DATA
        // transaction after NAK until Caliptra drains the first batch.
        configure_ep0_nak_retry_limit(10000);
        payload.delete();
        append_dword(
            payload,
            32'hC0DE_0000 | (32'(initial_status.fifo_size)));

        nak_before_overflow =
            caliptra_ss_usb_nak_monitor_callback::get_nak_count();
        indirect_fifo_data_try_write(
            payload, extra_result, "OCP_FIFO_RING_RETRIED_PUSH");
        nak_after_overflow =
            caliptra_ss_usb_nak_monitor_callback::get_nak_count();

        if (extra_result !== OCP_XFER_SUCCESS) begin
            `uvm_fatal("OCP_FIFO_RING",
                $sformatf("Automatically retried FIFO transfer ended with %s after %0d NAK retries.",
                          extra_result.name(),
                          nak_after_overflow - nak_before_overflow))
        end
        if (nak_after_overflow <= nak_before_overflow) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("No USB NAK observed while payload was unavailable to the host (before=%0d after=%0d).",
                          nak_before_overflow, nak_after_overflow))
        end

        empty_reached = 1'b0;
        for (int unsigned poll = 0;
             poll < OCP_FIFO_RING_MAX_EMPTY_POLLS; poll++) begin
            read_status(
                status,
                $sformatf("OCP_FIFO_RING_EMPTY_POLL_%0d", poll));
            if (status.empty &&
                (status.write_index === status.read_index) &&
                (visible_occupancy(status) === 0)) begin
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
            (visible_occupancy(status) !== 0)) begin
            `uvm_error("OCP_FIFO_RING",
                $sformatf("Final empty state invalid: EMPTY=%0b FULL=%0b WRITE_INDEX=%0d READ_INDEX=%0d occupancy=%0d.",
                          status.empty, status.full,
                          status.write_index, status.read_index,
                           visible_occupancy(status)))
        end

        // Publish the expected Device consumption count so the scoreboard can
        // optionally validate that exactly FIFO_SIZE DWORDs were read by firmware.
        uvm_config_db#(int unsigned)::set(
            null, "*", "ocp_expected_fifo_external_reads",
             initial_status.fifo_size + 1);
        publish_transfer_count();

        `uvm_info("OCP_FIFO_RING",
            $sformatf("FIFO batch test complete: FIFO_SIZE=%0d MAX_TRANSFER_SIZE=%0d USB_MAX_WR_BYTES=%0d retry_naks=%0d transfers=%0d.",
                      status.fifo_size,
                      status.max_transfer_dwords,
                      wMaxWrTransferSize,
                      nak_after_overflow - nak_before_overflow,
                      transfers_issued),
            UVM_NONE)
        #500us;
        `uvm_error("OCP_FIFO_RING",
            "Firmware did not end simulation within 500 us after FIFO drain.")
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_FIFO_RING_SEQUENCE_SV
