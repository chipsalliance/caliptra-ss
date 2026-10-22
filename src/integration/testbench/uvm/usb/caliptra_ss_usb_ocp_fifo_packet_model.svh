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

`ifndef CALIPTRA_SS_USB_OCP_FIFO_PACKET_MODEL_SVH
`define CALIPTRA_SS_USB_OCP_FIFO_PACKET_MODEL_SVH

// Transactional reference state. Capacity/limits and drain progress are inputs
// from protocol discovery or independently checked firmware evidence. This does
// not infer acceptance from a DUT index. OCP v1.1 Sections 8.2.5 and 9.2 define
// DWORD rounding; PING's maximum-packet capacity is a separate local policy.
class caliptra_ss_usb_ocp_fifo_packet_model extends uvm_object;
    `uvm_object_utils(caliptra_ss_usb_ocp_fifo_packet_model)

    protected int unsigned size_dwords;
    protected int unsigned maximum_transfer_bytes;
    protected int unsigned packet_bytes;
    protected int unsigned usable_bytes;
    protected int unsigned committed_bytes;
    protected int unsigned partial_bytes;
    protected int unsigned requested_bytes;
    protected int unsigned usb_write_limit;
    protected int unsigned image_bytes;
    protected int unsigned image_committed_bytes;
    protected bit request_limits_valid;
    protected int unsigned write_index;
    protected int unsigned read_index;
    protected bit batch_active;
    protected bit configured;
    protected bit consumed_generation_valid;
    protected logic [15:0] consumed_generation;

    function new(string name = "caliptra_ss_usb_ocp_fifo_packet_model");
        super.new(name);
    endfunction

    function void configure(
        input int unsigned fifo_size_dwords,
        input int unsigned max_transfer_dwords,
        input int unsigned ep0_packet_bytes,
        input bit reserve_ring_slot = 1'b1,
        input int unsigned usb_write_limit_bytes = 0,
        input int unsigned image_dwords = 0);
        if ((fifo_size_dwords < 2) || (max_transfer_dwords == 0) ||
            (ep0_packet_bytes == 0) ||
            (fifo_size_dwords > (32'hFFFF_FFFF / 4)) ||
            (max_transfer_dwords > (32'hFFFF_FFFF / 4)) ||
            (image_dwords > (32'hFFFF_FFFF / 4)) ||
            (usb_write_limit_bytes > 16'hFFFF))
            `uvm_fatal("OCP_FIFO_MODEL", "Invalid discovered FIFO/packet limits.")
        size_dwords = fifo_size_dwords;
        maximum_transfer_bytes = max_transfer_dwords * 4;
        packet_bytes = ep0_packet_bytes;
        usb_write_limit = usb_write_limit_bytes;
        image_bytes = image_dwords * 4;
        request_limits_valid = (usb_write_limit_bytes != 0);
        // reserve_ring_slot=0 explicitly selects the full-capacity
        // local deviation. It must not silently replace normative ring space.
        usable_bytes = (fifo_size_dwords - int'(reserve_ring_slot)) * 4;
        configured = 1'b1;
        reset();
    endfunction

    function void reset();
        committed_bytes = 0;
        partial_bytes = 0;
        requested_bytes = 0;
        image_committed_bytes = 0;
        write_index = 0;
        read_index = 0;
        batch_active = 1'b0;
    endfunction

    function int unsigned committed_byte_count();
        return committed_bytes;
    endfunction

    function int unsigned partial_byte_count();
        return partial_bytes;
    endfunction

    function bit lifecycle_idle();
        return configured && !batch_active;
    endfunction

    function int unsigned free_byte_count();
        return usable_bytes - committed_bytes - partial_bytes;
    endfunction

    function int unsigned next_packet_bytes();
        int unsigned remaining;
        if (!batch_active) return 0;
        remaining = requested_bytes - partial_bytes;
        return (remaining < packet_bytes) ? remaining : packet_bytes;
    endfunction

    function bit can_accept_next_packet();
        int unsigned next_size;
        next_size = next_packet_bytes();
        return configured && batch_active && (next_size != 0) &&
               (next_size <= free_byte_count());
    endfunction

    function bit can_ack_ping();
        return configured && (free_byte_count() >= packet_bytes);
    endfunction

    function void begin_batch(input int unsigned byte_count);
        if (!configured || batch_active || (byte_count == 0) ||
            (byte_count > maximum_transfer_bytes))
            `uvm_fatal("OCP_FIFO_MODEL", "Invalid batch start or overlapping batch.")
        requested_bytes = byte_count;
        partial_bytes = 0;
        batch_active = 1'b1;
    endfunction

    function void accept_packet(input int unsigned byte_count);
        if (!can_accept_next_packet() || (byte_count != next_packet_bytes()))
            `uvm_fatal("OCP_FIFO_MODEL", "Packet acceptance violates predicted capacity/length.")
        partial_bytes += byte_count;
    endfunction

    function void commit_batch();
        int unsigned rounded_bytes;
        rounded_bytes = ((partial_bytes + 3) / 4) * 4;
        if (!batch_active || (partial_bytes != requested_bytes) ||
            (rounded_bytes > (usable_bytes - committed_bytes)))
            `uvm_fatal("OCP_FIFO_MODEL", "Incomplete or over-capacity batch commit.")
        committed_bytes += rounded_bytes;
        image_committed_bytes += rounded_bytes;
        write_index = (write_index + rounded_bytes / 4) % size_dwords;
        batch_active = 1'b0;
        partial_bytes = 0;
        requested_bytes = 0;
    endfunction

    // An unrelated decoder abort cannot discard already committed FIFO data.
    // Only the current FIFO_DATA owner loses its uncommitted bytes.
    function void abort_batch(input bit owns_fifo_data);
        if (!owns_fifo_data) return;
        batch_active = 1'b0;
        partial_bytes = 0;
        requested_bytes = 0;
    endfunction

    function void drain(input int unsigned dwords);
        if (!configured || (dwords > (committed_bytes / 4)))
            `uvm_fatal("OCP_FIFO_MODEL", "Drain exceeds independently committed data.")
        committed_bytes -= dwords * 4;
        read_index = (read_index + dwords) % size_dwords;
    endfunction

    function bit indices_match(
        input int unsigned actual_write, input int unsigned actual_read);
        return configured && (actual_write == write_index) &&
               (actual_read == read_index);
    endfunction

    // These predicates are also used by deliberate invalid-history tests.
    // Drain counts and reset completion must come from independent evidence,
    // never from a difference between observed DUT indices.
    function bit observe_drain(input int unsigned dwords);
        if (!configured || (dwords == 0) ||
            (dwords > committed_bytes / 4)) return 1'b0;
        drain(dwords);
        return 1'b1;
    endfunction

    function bit observe_reset();
        if (!configured) return 1'b0;
        reset();
        return 1'b1;
    endfunction

    function bit observe_abort(input bit owns_fifo_data);
        if (!configured || (owns_fifo_data && !batch_active)) return 1'b0;
        abort_batch(owns_fifo_data);
        return 1'b1;
    endfunction

    // USB 2.0 8.5.3/8.5.2: ACK and NYET accept OUT DATA; NAK does
    // not. Data-toggle replay must not allocate space twice. OCP Recovery
    // v1.1 8.2.5/9.2: only a completed batch advances the DWORD write index.
    // One complete, generation-qualified EP0 OUT request is consumed once.
    // No transfer-success flag or DUT write index can manufacture acceptance.
    function bit observe_window(
        input caliptra_ss_usb_ocp_arbiter_packet_callback packets,
        input logic [15:0] generation,
        input bit [6:0] address,
        input int unsigned byte_count,
        input bit acceptance_allowed,
        input bit owner_abort = 1'b0,
        input bit unrelated_abort = 1'b0);
        typedef caliptra_ss_usb_ocp_arbiter_packet_callback cb_t;
        cb_t::packet_record_t r;
        typedef enum {WAIT_SETUP, IDLE, OUT_DATA, OUT_REPLY,
                      PING_REPLY, STATUS_DATA, STATUS_ACK, DONE} state_e;
        state_e state;
        svt_usb_packet::pid_name_enum data_pid;
        svt_usb_packet::pid_name_enum expected_pid;
        int unsigned data_bytes;
        int unsigned previous_bytes;
        bit data_bad;
        bit have_previous;
        bit saw_stall;
        logic [15:0] generation_distance;

        generation_distance = generation - consumed_generation;
        if (!configured || !request_limits_valid || batch_active ||
            (owner_abort && unrelated_abort) ||
            (packets == null) ||
            packets.overflowed() || $isunknown(generation) ||
            (consumed_generation_valid &&
             ((generation_distance == 0) || generation_distance[15])) ||
            (acceptance_allowed &&
             ((byte_count == 0) || (byte_count > maximum_transfer_bytes) ||
              (byte_count > usb_write_limit) ||
              (byte_count > (image_bytes - image_committed_bytes)))))
            return 1'b0;
        consumed_generation_valid = 1'b1;
        consumed_generation = generation;
        state = WAIT_SETUP;
        expected_pid = svt_usb_packet::DATA1;
        have_previous = 1'b0;
        previous_bytes = 0;
        saw_stall = 1'b0;
        if (packets.accepted_setup_count() != 1) return 1'b0;
        for (int unsigned i = 0; i < packets.packet_count(); i++) begin
            r = packets.get_packet(i);
            if (!(r.generation === generation)) return 1'b0;
            if (r.pid_name === svt_usb_packet::SOF) continue;
            if (state == WAIT_SETUP) begin
                if (!r.accepted_setup) continue;
                if (!r.target_valid || !(r.device_address === address) ||
                    !(r.endpoint_number === 4'd0)) return 1'b0;
                if (acceptance_allowed) begin_batch(byte_count);
                state = IDLE;
                continue;
            end
            if (!r.target_valid || !(r.device_address === address) ||
                !(r.endpoint_number === 4'd0) || (state == DONE))
                return 1'b0;
            case (state)
                IDLE: begin
                    if (!(r.direction === cb_t::PACKET_TX) ||
                        r.crc_error_detected || r.data_error_detected)
                        return 1'b0;
                    case (r.pid_name)
                        svt_usb_packet::OUT: state = OUT_DATA;
                        svt_usb_packet::PING: state = PING_REPLY;
                        svt_usb_packet::IN: state = STATUS_DATA;
                        default: return 1'b0;
                    endcase
                end
                OUT_DATA: begin
                    if (!(r.direction === cb_t::PACKET_TX) ||
                        !((r.pid_name === svt_usb_packet::DATA0) ||
                          (r.pid_name === svt_usb_packet::DATA1)))
                        return 1'b0;
                    data_pid = r.pid_name;
                    data_bytes = r.data_length;
                    data_bad = r.crc_error_detected || r.data_error_detected;
                    state = OUT_REPLY;
                end
                OUT_REPLY: begin
                    // A missing/corrupted handshake cannot prove acceptance.
                    // Resume only at a new token; leave the expected toggle.
                    if (r.direction === cb_t::PACKET_TX) begin
                        if (r.crc_error_detected || r.data_error_detected)
                            return 1'b0;
                        if (r.pid_name === svt_usb_packet::OUT)
                            state = OUT_DATA;
                        else if (r.pid_name === svt_usb_packet::PING)
                            state = PING_REPLY;
                        else return 1'b0;
                        continue;
                    end
                    if ((r.direction === cb_t::PACKET_RX) &&
                        (r.crc_error_detected || r.data_error_detected))
                        continue;
                    if (!(r.direction === cb_t::PACKET_RX) ||
                        r.crc_error_detected || r.data_error_detected)
                        return 1'b0;
                    case (r.pid_name)
                        svt_usb_packet::ACK, svt_usb_packet::NYET: begin
                            if (!acceptance_allowed || data_bad) return 1'b0;
                            if (data_pid === expected_pid) begin
                                if (!can_accept_next_packet() ||
                                    (data_bytes != next_packet_bytes()))
                                    return 1'b0;
                                accept_packet(data_bytes);
                                previous_bytes = data_bytes;
                                have_previous = 1'b1;
                                expected_pid = (expected_pid === svt_usb_packet::DATA1) ?
                                    svt_usb_packet::DATA0 : svt_usb_packet::DATA1;
                            end else if (!have_previous ||
                                         (data_bytes != previous_bytes))
                                return 1'b0;
                            state = IDLE;
                        end
                        svt_usb_packet::NAK: state = IDLE;
                        svt_usb_packet::STALL: begin
                            saw_stall = 1'b1;
                            state = DONE;
                        end
                        default: return 1'b0;
                    endcase
                end
                PING_REPLY: begin
                    if (!(r.direction === cb_t::PACKET_RX) ||
                        r.crc_error_detected || r.data_error_detected)
                        return 1'b0;
                    case (r.pid_name)
                        svt_usb_packet::ACK: begin
                            if (!acceptance_allowed || !can_ack_ping()) return 1'b0;
                            state = IDLE;
                        end
                        svt_usb_packet::NAK: state = IDLE;
                        svt_usb_packet::STALL: begin
                            saw_stall = 1'b1;
                            state = DONE;
                        end
                        default: return 1'b0;
                    endcase
                end
                STATUS_DATA: begin
                    if ((r.direction === cb_t::PACKET_TX) &&
                        (r.pid_name === svt_usb_packet::IN) &&
                        !r.crc_error_detected && !r.data_error_detected)
                        continue;
                    if ((r.direction === cb_t::PACKET_RX) &&
                        (r.crc_error_detected || r.data_error_detected))
                        continue;
                    if (!(r.direction === cb_t::PACKET_RX) ||
                        r.crc_error_detected || r.data_error_detected)
                        return 1'b0;
                    if (r.pid_name === svt_usb_packet::NAK) state = IDLE;
                    else if (r.pid_name === svt_usb_packet::STALL) begin
                        saw_stall = 1'b1;
                        state = DONE;
                    end else if ((r.pid_name === svt_usb_packet::DATA1) &&
                                 (r.data_length == 0) && acceptance_allowed &&
                                 (partial_bytes == requested_bytes))
                        state = STATUS_ACK;
                    else return 1'b0;
                end
                STATUS_ACK: begin
                    if ((r.direction === cb_t::PACKET_TX) &&
                        (r.pid_name === svt_usb_packet::IN) &&
                        !r.crc_error_detected && !r.data_error_detected) begin
                        state = STATUS_DATA;
                        continue;
                    end
                    if (!(r.direction === cb_t::PACKET_TX) ||
                        !(r.pid_name === svt_usb_packet::ACK) ||
                        r.crc_error_detected || r.data_error_detected ||
                        owner_abort) return 1'b0;
                    // DWORD padding consumes space even for a short packet.
                    if ((((partial_bytes + 3) / 4) * 4) >
                        (usable_bytes - committed_bytes)) return 1'b0;
                    commit_batch();
                    state = DONE;
                end
                default: return 1'b0;
            endcase
        end
        if (saw_stall || owner_abort) begin
            if (acceptance_allowed && !observe_abort(1'b1)) return 1'b0;
            return saw_stall || (state != WAIT_SETUP);
        end
        // An explicitly interrupted observation can preserve an outstanding
        // FIFO owner. It must subsequently receive owner-abort/reset evidence;
        // a new FIFO request cannot silently overwrite that partial batch.
        if (unrelated_abort && (state != WAIT_SETUP))
            return observe_abort(1'b0);
        return (state == DONE) && !batch_active;
    endfunction
endclass

`endif
