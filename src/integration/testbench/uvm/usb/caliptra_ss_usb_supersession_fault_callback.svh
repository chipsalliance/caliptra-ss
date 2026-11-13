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
//
`ifndef CALIPTRA_SS_USB_SUPERSESSION_FAULT_CALLBACK_SVH
`define CALIPTRA_SS_USB_SUPERSESSION_FAULT_CALLBACK_SVH

// Serialized, test-local SETUP fault injection. Bind the protocol's actual
// started transfer, not the submitted sequence item (which may be copied).
class caliptra_ss_usb_supersession_fault_callback extends svt_usb_protocol_callbacks;
    `uvm_object_utils(caliptra_ss_usb_supersession_fault_callback)
    // USB 2.0 Sec 8.3.1, Table 8-1: PID nibble followed by its complement.
    localparam logic [7:0] DATA0_PID = 8'hC3;
    localparam logic [7:0] SOF_PID = 8'hA5;
    bit armed, short_setup, fired, setup_ended, transfer_finished;
    int bindings, injections, dropped_descriptors, setup_transaction_ix;
    logic [15:0] generation;
    logic [63:0] expected_setup;
    logic [6:0] address;
    svt_usb_transfer actual_transfer;
    svt_usb_packet actual_packet;
    caliptra_ss_usb_supersession_checker sink;
    logic [7:0] tx_bytes[$];
    bit tx_sop_seen, tx_eop_seen, tx_capture_closed;
    int tx_items;
    bit tx_frame_active, tx_frame_pid_valid;
    logic [7:0] tx_frame_pid;
    int tx_frame_items;

    function new(string name = "caliptra_ss_usb_supersession_fault_callback");
        super.new(name);
    endfunction

    function void ocp_supersession_configure_fault_window(input logic [15:0] gen, input logic [6:0] addr,
                      input logic [63:0] setup_bytes, input bit shorten);
        if (armed || (sink == null))
            `uvm_fatal("SUPERSESSION_FAULT", "Overlapping fault window or missing boundary checker")
        generation = gen;
        address = addr;
        expected_setup = setup_bytes;
        short_setup = shorten;
        armed = 1;
        fired = 0;
        setup_ended = 0;
        transfer_finished = 0;
        bindings = 0;
        injections = 0;
        dropped_descriptors = 0;
        setup_transaction_ix = -1;
        actual_transfer = null;
        actual_packet = null;
        tx_bytes.delete();
        tx_sop_seen = 0;
        tx_eop_seen = 0;
        tx_capture_closed = 0;
        tx_items = 0;
    endfunction

    virtual function void transfer_started(svt_usb_protocol component,
                                           svt_usb_transfer transfer);
        if (!armed || (transfer == null)) return;
        if ((transfer.xfer_type != svt_usb_transfer::CONTROL_TRANSFER) ||
            (transfer.endpoint_number != 0) || (transfer.device_address != address) ||
            (caliptra_ss_usb_supersession_checker::ocp_supersession_get_setup_line(transfer) !== expected_setup))
            `uvm_fatal("SUPERSESSION_FAULT", "Unexpected transfer in serialized fault-binding window")
        if (actual_transfer != null)
            `uvm_fatal("SUPERSESSION_FAULT", "More than one actual transfer started in fault window")
        actual_transfer = transfer;
        bindings++;
        if ((transfer.cfg == null) || (transfer.cfg.remote_device_cfg.size() == 0) ||
            (transfer.cfg.remote_device_cfg[0].endpoint_cfg.size() == 0))
            `uvm_fatal("SUPERSESSION_FAULT", "Actual transfer has no remote EP0 retry configuration")
        if ((transfer.cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_timeout != 0) ||
            (transfer.cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_error != 0) ||
            (transfer.cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_nak != 0) ||
            (transfer.cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_stall != 0))
            `uvm_fatal("SUPERSESSION_FAULT", "Actual remote EP0 retries were not disabled for one attempt")
    endfunction

    virtual function void pre_usb_20_packet_out_port_put(
        svt_usb_protocol component, int chan_id, svt_usb_packet packet,
        svt_usb_transaction transaction, int packet_ix, svt_usb_transfer transfer,
        int transaction_ix, ref bit drop);
        svt_usb_packet_exception exception_item;
        logic [63:0] nominal_setup;
        bit [7:0] payload_bytes[];
        int unsigned total;
        if (!armed) return;
        if ((transfer == null) || (transfer != actual_transfer)) return;
        if (packet == null)
            `uvm_fatal("SUPERSESSION_FAULT", "Null packet in packet-output callback")
        // A fired latch alone would allow a later retry to transmit cleanly.
        // Keep this guard armed through clean retirement.
        if (fired) begin
            drop = 1;
            dropped_descriptors++;
            return;
        end
        if ((transaction == null) ||
            (transaction.xact_type != svt_usb_types::SETUP_TRANSACTION) ||
            (packet.speed != svt_usb_types::HS) ||
            (packet.pid_type != svt_usb_packet::DATA) ||
            (packet.pid_name != svt_usb_packet::DATA0)) return;
        // Packet-level error/exception query, not transfer results or the
        // packet's processing-state status. Do not filter for protocol use.
        if (drop || (packet.get_payload_byte_count() != 8) ||
            (packet.is_pkt_error_free(0, 0) !== 1'b1) ||
            (packet.get_crc16_val(1) !== packet.get_crc16_val(0)))
            `uvm_fatal("SUPERSESSION_FAULT", "Selected SETUP DATA0 was not initially error-free/eight bytes")
        if ((packet_ix < 0) || (transaction_ix < 0) ||
            (packet.payload == null) || (packet.payload_offset < 0))
            `uvm_fatal("SUPERSESSION_FAULT", "Selected SETUP has no valid actual transaction/payload binding")
        total = packet.payload.get_pack_byte_cnt();
        if ((packet.payload_offset > total) ||
            (8 > total - packet.payload_offset) ||
            !packet.payload.get_bytes(packet.payload_offset, 8, payload_bytes) ||
            (payload_bytes.size() != 8))
            `uvm_fatal("SUPERSESSION_FAULT", "Selected SETUP payload bytes are unavailable")
        for (int i = 0; i < 8; i++)
            nominal_setup[i*8 +: 8] = payload_bytes[i];
        if (nominal_setup !== expected_setup)
            `uvm_fatal("SUPERSESSION_FAULT", "Actual SETUP packet does not contain the bound request bytes")
        exception_item = svt_usb_packet_exception::type_id::create("setup_exception");
        exception_item.xact = packet;
        exception_item.retry_number = 0;
        if (short_setup) begin
            // SHORT_PACKET_ERROR removes N payload bytes, then regenerates
            // CRC16. It does not change SETUP.wLength (USB 2.0 8.5.3).
            exception_item.error_kind = svt_usb_packet_exception::LENGTH_ERROR;
            exception_item.length_error = svt_usb_packet_exception::SHORT_PACKET_ERROR;
            exception_item.byte_offset = 4;
        end else begin
            exception_item.error_kind = svt_usb_packet_exception::CRC_ERROR;
            exception_item.crc_error = svt_usb_packet_exception::CRC16_ERROR;
            exception_item.mask_or_value = 32'h1;
        end
        if (packet.exception_list == null)
            packet.exception_list =
                svt_usb_packet_exception_list::type_id::create("setup_exception_list");
        packet.exception_list.add_exception(exception_item);
        actual_packet = packet;
        sink.ocp_supersession_configure_fault(generation, actual_transfer, packet, short_setup);
        setup_transaction_ix = transaction_ix;
        fired = 1;
        injections++;
        `uvm_info("SUPERSESSION_FAULT", $sformatf(
            "gen=%0d short=%0b attached to actual SETUP transaction=%0d packet=%0d",
            generation, short_setup, transaction_ix, packet_ix), UVM_NONE)
    endfunction

    function void ocp_supersession_check_tx_data(input svt_usb_data data, input bit drop);
        bit guarded, byte_valid;
        logic [7:0] value;
        guarded = armed && fired;
        if ((data == null) || drop) begin
            if (guarded)
                `uvm_fatal("SUPERSESSION_FAULT", "Null or dropped data in serialized TX window")
            return;
        end
        // USB2 descriptors need not populate parent_link_object. Track framing
        // continuously so even a SOF spanning guard activation is recognized.
        // Only the first byte after SOP is a PID, never a payload byte.
        if (data.is_sop) begin
            if (guarded && tx_frame_active) begin
                `uvm_fatal("SUPERSESSION_FAULT", "Overlapping SOP in serialized TX window")
                return;
            end
            tx_frame_active = 1;
            tx_frame_pid_valid = 0;
            tx_frame_items = 0;
        end
        if (!tx_frame_active) begin
            if (guarded)
                `uvm_fatal("SUPERSESSION_FAULT", "Serialized TX descriptor has no SOP")
            return;
        end
        tx_frame_items++;
        byte_valid = data.is_byte_data && data.get_data_valid_val();
        if (byte_valid) begin
            value = data.get_data_val();
            if (!tx_frame_pid_valid) begin
                tx_frame_pid = value;
                tx_frame_pid_valid = 1;
            end
        end
        if (guarded && tx_frame_pid_valid) begin
            if (tx_frame_pid != SOF_PID) begin
                if (tx_frame_pid != DATA0_PID) begin
                    `uvm_fatal("SUPERSESSION_FAULT", "Unexpected packet in serialized TX window")
                    return;
                end
                if (tx_capture_closed || tx_eop_seen) begin
                    `uvm_fatal("SUPERSESSION_FAULT", "Additional DATA0 output after bound frame completion")
                    return;
                end
                tx_sop_seen = 1;
                tx_items = tx_frame_items;
                if (byte_valid) begin
                    if (data.valid_data_field != svt_usb_data::DATA)
                        `uvm_fatal("SUPERSESSION_FAULT", "Bound SETUP byte lacks byte representation")
                    tx_bytes.push_back(value);
                end
                if (data.is_eop) tx_eop_seen = 1;
            end
        end
        if (data.is_eop) begin
            if (guarded && !tx_frame_pid_valid)
                `uvm_fatal("SUPERSESSION_FAULT", "Serialized TX frame ended without a PID")
            tx_frame_active = 0;
        end
    endfunction

    function void ocp_supersession_configure_tx_capture_completion();
        if (!armed || !fired || (actual_packet == null) || tx_capture_closed)
            `uvm_fatal("SUPERSESSION_FAULT", "Invalid serialized TX capture completion")
        tx_capture_closed = 1;
    endfunction

    virtual function void transaction_ended(svt_usb_protocol component,
        svt_usb_transfer transfer, int transaction_ix);
        if (armed && fired && (transfer == actual_transfer) &&
            (transaction_ix == setup_transaction_ix)) setup_ended = 1;
    endfunction

    virtual function void transfer_ended(svt_usb_protocol component,
                                         svt_usb_transfer transfer);
        if (armed && (transfer != null) && (transfer == actual_transfer))
            transfer_finished = 1;
    endfunction

    function void ocp_supersession_configure_fault_retirement();
        if (!setup_ended || !transfer_finished)
            `uvm_fatal("SUPERSESSION_FAULT", "Fault guard removed before transaction/transfer retirement")
        armed = 0;
        actual_transfer = null;
        actual_packet = null;
    endfunction
endclass

class caliptra_ss_usb_supersession_tx_callback extends svt_usb_link_callback;
    `uvm_object_utils(caliptra_ss_usb_supersession_tx_callback)
    caliptra_ss_usb_supersession_fault_callback source;

    function new(string name = "caliptra_ss_usb_supersession_tx_callback");
        super.new(name);
    endfunction

    virtual function void pre_usb_20_data_out_port_put(
        svt_usb_link component, int chan_id, svt_usb_data data, ref bit drop);
        if (source == null)
            `uvm_fatal("SUPERSESSION_FAULT", "Missing serialized-byte observation context")
        source.ocp_supersession_check_tx_data(data, drop);
    endfunction
endclass
`endif
