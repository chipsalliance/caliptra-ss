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

`ifndef CALIPTRA_SS_USB_OCP_ARBITER_PACKET_CALLBACK_SV
`define CALIPTRA_SS_USB_OCP_ARBITER_PACKET_CALLBACK_SV

// Captures packet-level evidence for one generation-qualified arbiter
// observation window. The isolation checker uses transfer-level ownership and
// legacy-state invariants; later control-phasing tests reuse these packet
// records to distinguish ACK, NAK, STALL, DATA, and zero-length packets.
class caliptra_ss_usb_ocp_arbiter_packet_callback
    extends svt_usb_link_monitor_callback;

    `uvm_object_utils(caliptra_ss_usb_ocp_arbiter_packet_callback)

    typedef enum bit {
        PACKET_RX,
        PACKET_TX
    } packet_direction_e;

    typedef struct {
        logic [15:0] generation;
        packet_direction_e direction;
        svt_usb_packet::pid_type_enum pid_type;
        svt_usb_packet::pid_name_enum pid_name;
        bit setup_bit;
        bit [6:0] device_address;
        bit [3:0] endpoint_number;
        bit [15:0] data_length;
        int retry_number;
        realtime observed_at;
        bit target_valid;
        // Exception detectors are evidence, not an independent CRC calculation.
        bit crc_error_detected;
        bit data_error_detected;
        bit accepted_setup;
        bit setup_data;
    } packet_record_t;

    localparam int unsigned MAX_PACKET_RECORDS = 4096;
    protected packet_record_t packet_records[$];
    protected int unsigned retained_packet_count;
    protected bit records_overflowed;
    protected int unsigned window_serial;
    protected bit token_target_valid;
    protected bit [6:0] token_address;
    protected bit [3:0] token_endpoint;
    protected bit pending_setup_token;
    protected bit pending_setup_data;
    protected bit diagnostics_enabled;
    protected int unsigned wait_timeouts;
    protected int unsigned explicit_aborts;
    protected int unsigned corrupted_packets;
    protected bit active;
    protected logic [15:0] active_generation;
    protected bit stage_trigger_active;
    protected svt_usb_transfer::xfer_stage_enum target_stage;
    protected bit setup_ack_seen;
    protected bit data_stage_started;
    protected bit data_packet_seen;
    protected uvm_event stage_observed;
    // Live setup-stage-ACK trigger. Firmware-error trigger sequences arm
    // this before issuing a claimed control-OUT SETUP and use it to
    // synchronize the abort/replacement-SETUP window without polling
    // packet_records. Kept independent of stage_trigger_active so it can
    // coexist with the existing DATA/STATUS-stage triggers used by ARB006.
    protected bit setup_ack_trigger_active;
    protected bit setup_ack_trigger_seen;
    protected uvm_event setup_ack_observed;

    function new(
        string name = "caliptra_ss_usb_ocp_arbiter_packet_callback");
        super.new(name);
        active = 1'b0;
        active_generation = '0;
        stage_trigger_active = 1'b0;
        setup_ack_seen = 1'b0;
        data_stage_started = 1'b0;
        data_packet_seen = 1'b0;
        stage_observed = new("stage_observed");
        setup_ack_trigger_active = 1'b0;
        setup_ack_observed = new("setup_ack_observed");
        window_serial = 0;
        retained_packet_count = 0;
        diagnostics_enabled = 1'b0;
        wait_timeouts = 0;
        explicit_aborts = 0;
        corrupted_packets = 0;
        reset_semantics();
    endfunction

    protected function void reset_semantics();
        stage_trigger_active = 1'b0;
        setup_ack_seen = 1'b0;
        data_stage_started = 1'b0;
        data_packet_seen = 1'b0;
        setup_ack_trigger_active = 1'b0;
        setup_ack_trigger_seen = 1'b0;
        pending_setup_token = 1'b0;
        pending_setup_data = 1'b0;
        token_target_valid = 1'b0;
        token_address = '0;
        token_endpoint = '0;
        stage_observed.reset();
        setup_ack_observed.reset();
    endfunction

    function void start_window(input logic [15:0] generation);
        packet_records.delete();
        retained_packet_count = 0;
        records_overflowed = 1'b0;
        wait_timeouts = 0;
        explicit_aborts = 0;
        corrupted_packets = 0;
        window_serial++;
        reset_semantics();
        active_generation = generation;
        active = 1'b1;
    endfunction

    function void stop_window();
        active = 1'b0;
        window_serial++;
        // Keep immutable packet evidence available to post-window checkers.
        reset_semantics();
    endfunction

    // Arm the live setup-stage-ACK event. The event triggers on the next
    // RX ACK that follows a TX SETUP token immediately followed by a
    // TX 8-byte DATA0. A pending SETUP+DATA0 pair is discarded and the
    // tracker restarted if any packet arrives out of order between them.
    function void arm_setup_ack_trigger();
        setup_ack_trigger_seen = 1'b0;
        setup_ack_observed.reset();
        setup_ack_trigger_active = 1'b1;
    endfunction

    task wait_for_setup_ack_trigger(
        input time timeout,
        output bit observed);

        int unsigned serial;
        serial = window_serial;
        observed = active && setup_ack_trigger_seen;
        if (observed) return;
        fork : setup_ack_trigger_timeout
            begin
                wait (setup_ack_trigger_seen || !active ||
                      (window_serial != serial));
            end
            begin
                #(timeout);
            end
        join_any
        disable setup_ack_trigger_timeout;
        observed = active && (window_serial == serial) &&
                   setup_ack_trigger_seen;
        if (!observed && diagnostics_enabled && active &&
            (window_serial == serial)) wait_timeouts++;
    endtask

    // A level-sensitive wait observes packets that arrived before this call
    // or before its fork starts. Window replacement/stop cancels old waiters.
    task wait_for_packet_count(
        input int unsigned minimum,
        input time timeout,
        output bit observed);

        int unsigned serial;
        serial = window_serial;
        observed = active && (retained_packet_count >= minimum);
        if (observed) return;
        fork : packet_count_timeout
            begin
                wait ((retained_packet_count >= minimum) || !active ||
                      (window_serial != serial));
            end
            begin
                #(timeout);
            end
        join_any
        disable packet_count_timeout;
        observed = active && (window_serial == serial) &&
                   (retained_packet_count >= minimum);
        if (!observed && diagnostics_enabled && active &&
            (window_serial == serial)) wait_timeouts++;
    endtask

    function void enable_diagnostics(input bit enable = 1'b1);
        diagnostics_enabled = enable;
    endfunction

    // Explicit transport aborts are stimulus-side markers, not inferred from
    // silence. Do not allow a late ACK to complete an aborted transaction.
    function void note_abort();
        if (!active) return;
        if (diagnostics_enabled) explicit_aborts++;
        pending_setup_token = 1'b0;
        pending_setup_data = 1'b0;
        token_target_valid = 1'b0;
        setup_ack_seen = 1'b0;
        data_stage_started = 1'b0;
        data_packet_seen = 1'b0;
    endfunction

    function int unsigned timeout_count();
        return wait_timeouts;
    endfunction

    function int unsigned abort_count();
        return explicit_aborts;
    endfunction

    function int unsigned corruption_count();
        return corrupted_packets;
    endfunction

    function void arm_stage_trigger(
        input svt_usb_transfer::xfer_stage_enum stage);

        target_stage = stage;
        setup_ack_seen = 1'b0;
        data_stage_started = 1'b0;
        data_packet_seen = 1'b0;
        stage_observed.reset();
        stage_trigger_active = 1'b1;
    endfunction

    task wait_for_stage_trigger(
        input time timeout,
        output bit observed);

        observed = 1'b0;
        fork : stage_trigger_timeout
            begin
                stage_observed.wait_trigger();
                observed = 1'b1;
            end
            begin
                #(timeout);
            end
        join_any
        disable stage_trigger_timeout;
    endtask

    function int unsigned packet_count();
        return packet_records.size();
    endfunction

    function packet_record_t get_packet(input int unsigned index);
        return packet_records[index];
    endfunction

    function int unsigned count_pid(
        input svt_usb_packet::pid_name_enum pid_name,
        input packet_direction_e direction);

        int unsigned count;
        count = 0;
        foreach (packet_records[index]) begin
            if ((packet_records[index].pid_name == pid_name) &&
                (packet_records[index].direction == direction)) begin
                count++;
            end
        end
        return count;
    endfunction

    function int unsigned count_zlp(input packet_direction_e direction);
        int unsigned count;
        count = 0;
        foreach (packet_records[index]) begin
            if ((packet_records[index].direction == direction) &&
                ((packet_records[index].pid_name == svt_usb_packet::DATA0) ||
                 (packet_records[index].pid_name == svt_usb_packet::DATA1)) &&
                (packet_records[index].data_length == 0)) begin
                count++;
            end
        end
        return count;
    endfunction

    function bit setup_stage_acked();
        return accepted_setup_count() != 0;
    endfunction

    function int unsigned accepted_setup_count();
        int unsigned count;
        count = 0;
        foreach (packet_records[index])
            if (packet_records[index].accepted_setup) count++;
        return count;
    endfunction

    function bit overflowed();
        return records_overflowed;
    endfunction

    // Pure predicate: mutation tests can reject bad evidence without emitting
    // expected UVM_ERRORs. The sequence/scoreboard owns failure reporting.
    // USB 2.0 8.5.3.4: OUT requires its data packet before the STALL.
    function bit validate_stall_probe(
        input svt_usb_packet::pid_name_enum pid,
        input bit [6:0] address,
        input bit [3:0] endpoint,
        input int unsigned first_record = 0);

        int unsigned tokens;
        int unsigned stalls;
        int unsigned data_packets;
        bit valid;
        bit probe_pending;
        tokens = 0;
        stalls = 0;
        data_packets = 0;
        valid = !records_overflowed;
        probe_pending = 1'b0;
        if (!((pid === svt_usb_packet::IN) ||
              (pid === svt_usb_packet::OUT) ||
              (pid === svt_usb_packet::PING))) return 1'b0;
        foreach (packet_records[index]) begin
            if (index < first_record) continue;
            if (!(packet_records[index].generation === active_generation))
                valid = 1'b0;
            if (packet_records[index].pid_name === svt_usb_packet::SOF)
                continue;
            // A probe window must not contain a SETUP, even at another EP.
            if (packet_records[index].pid_name === svt_usb_packet::SETUP)
                valid = 1'b0;
            if ((packet_records[index].pid_type === svt_usb_packet::TOKEN) ||
                (packet_records[index].pid_type === svt_usb_packet::EXT_TOKEN) ||
                ((packet_records[index].pid_type === svt_usb_packet::SPECIAL) &&
                 (packet_records[index].pid_name === svt_usb_packet::PING))) begin
                // Any intervening token terminates the adjacent transaction.
                probe_pending = 1'b0;
                if (packet_records[index].target_valid &&
                    (packet_records[index].device_address === address) &&
                    (packet_records[index].endpoint_number === endpoint)) begin
                    tokens++;
                    if ((packet_records[index].direction === PACKET_TX) &&
                        (packet_records[index].pid_name === pid) &&
                        (((pid === svt_usb_packet::PING) &&
                          (packet_records[index].pid_type === svt_usb_packet::SPECIAL)) ||
                         (!(pid === svt_usb_packet::PING) &&
                          (packet_records[index].pid_type === svt_usb_packet::TOKEN))) &&
                        !packet_records[index].crc_error_detected &&
                        !packet_records[index].data_error_detected)
                        probe_pending = 1'b1;
                    else valid = 1'b0;
                end
                continue;
            end
            if (!packet_records[index].target_valid ||
                !(packet_records[index].device_address === address) ||
                !(packet_records[index].endpoint_number === endpoint))
                continue;
            if ((packet_records[index].direction === PACKET_RX) &&
                ((packet_records[index].pid_name === svt_usb_packet::ACK) ||
                 (packet_records[index].pid_name === svt_usb_packet::NAK) ||
                 (packet_records[index].pid_name === svt_usb_packet::NYET) ||
                 (packet_records[index].pid_type === svt_usb_packet::DATA)))
                valid = 1'b0;
            if ((packet_records[index].direction === PACKET_TX) &&
                ((packet_records[index].pid_name === svt_usb_packet::DATA0) ||
                 (packet_records[index].pid_name === svt_usb_packet::DATA1)) &&
                (pid === svt_usb_packet::OUT) && probe_pending &&
                (stalls == 0) && (data_packets == 0) &&
                !packet_records[index].crc_error_detected &&
                !packet_records[index].data_error_detected) begin
                data_packets++;
            end else if ((packet_records[index].direction === PACKET_RX) &&
                         (packet_records[index].pid_name === svt_usb_packet::STALL)) begin
                stalls++;
                if (!probe_pending ||
                    ((pid === svt_usb_packet::OUT) && (data_packets != 1)) ||
                    packet_records[index].crc_error_detected ||
                    packet_records[index].data_error_detected) valid = 1'b0;
                probe_pending = 1'b0;
            end else begin
                // No packet may separate the token/data/STALL beats.
                valid = 1'b0;
                probe_pending = 1'b0;
            end
        end
        return valid && (tokens == 1) && (stalls == 1) &&
               (!(pid === svt_usb_packet::OUT) || (data_packets == 1));
    endfunction

    function bit validate_control_stall(
        input bit [6:0] address, input bit [3:0] endpoint);
        int token_index;
        bit setup_accepted;
        token_index = -1;
        setup_accepted = 1'b0;
        if (records_overflowed || (accepted_setup_count() != 1)) return 1'b0;
        foreach (packet_records[index]) begin
            if (packet_records[index].accepted_setup) begin
                if (!packet_records[index].target_valid ||
                    (packet_records[index].device_address != address) ||
                    (packet_records[index].endpoint_number != endpoint))
                    return 1'b0;
                setup_accepted = 1'b1;
            end
            if (packet_records[index].pid_name == svt_usb_packet::SOF)
                continue;
            if ((packet_records[index].pid_type == svt_usb_packet::TOKEN) ||
                (packet_records[index].pid_type == svt_usb_packet::EXT_TOKEN) ||
                ((packet_records[index].pid_type == svt_usb_packet::SPECIAL) &&
                 (packet_records[index].pid_name == svt_usb_packet::PING)))
                token_index = setup_accepted ? int'(index) : -1;
            if ((packet_records[index].direction == PACKET_RX) &&
                (packet_records[index].pid_name == svt_usb_packet::STALL)) begin
                if (token_index < 0) return 1'b0;
                // Validate the complete rejecting transaction and all later
                // packets, not an unattributed STALL anywhere in the window.
                return validate_stall_probe(packet_records[token_index].pid_name,
                    address, endpoint, token_index);
            end
        end
        return 1'b0;
    endfunction

    function bit check_stall_probe(
        input svt_usb_packet::pid_name_enum pid,
        input bit [6:0] address,
        input bit [3:0] endpoint,
        input string label);

        return validate_stall_probe(pid, address, endpoint);
    endfunction

    function bit get_last_rx_data_length(output int unsigned data_length);
        for (int index = packet_records.size() - 1; index >= 0; index--) begin
            if ((packet_records[index].direction == PACKET_RX) &&
                ((packet_records[index].pid_name == svt_usb_packet::DATA0) ||
                 (packet_records[index].pid_name == svt_usb_packet::DATA1))) begin
                data_length = packet_records[index].data_length;
                return 1'b1;
            end
        end
        data_length = 0;
        return 1'b0;
    endfunction

    function bit get_setup_timestamp(output realtime setup_time);
        foreach (packet_records[index]) begin
            if (packet_records[index].setup_data) begin
                setup_time = packet_records[index].observed_at;
                return 1'b1;
            end
        end
        setup_time = 0.0;
        return 1'b0;
    endfunction

    function bit legacy_out_stage_completed();
        bit out_token_seen;
        bit out_data_seen;

        out_token_seen = 1'b0;
        out_data_seen = 1'b0;
        foreach (packet_records[index]) begin
            if ((packet_records[index].direction == PACKET_TX) &&
                (packet_records[index].pid_name == svt_usb_packet::OUT)) begin
                out_token_seen = 1'b1;
                out_data_seen = 1'b0;
                continue;
            end
            if (out_token_seen &&
                (packet_records[index].direction == PACKET_TX) &&
                ((packet_records[index].pid_name == svt_usb_packet::DATA0) ||
                 (packet_records[index].pid_name == svt_usb_packet::DATA1))) begin
                out_data_seen = 1'b1;
                continue;
            end
            if (out_data_seen &&
                (packet_records[index].direction == PACKET_RX) &&
                ((packet_records[index].pid_name == svt_usb_packet::ACK) ||
                 (packet_records[index].pid_name == svt_usb_packet::NYET))) begin
                return 1'b1;
            end
        end
        return 1'b0;
    endfunction

    protected function void record_packet(
        input packet_direction_e direction,
        input svt_usb_packet pkt);

        packet_record_t record;

        if (!active || (pkt == null)) begin
            return;
        end
        // Retain the first bounded window and fail closed on truncation.
        if (packet_records.size() >= MAX_PACKET_RECORDS) begin
            records_overflowed = 1'b1;
            pending_setup_token = 1'b0;
            pending_setup_data = 1'b0;
            return;
        end

        record = '{generation:'0, direction:PACKET_RX,
                   pid_type:svt_usb_packet::TOKEN,
                   pid_name:svt_usb_packet::OUT, default:0};
        record.generation = active_generation;
        record.direction = direction;
        record.pid_type = pkt.pid_type;
        record.pid_name = pkt.pid_name;
        record.setup_bit = pkt.get_setup_bit_val();
        // USB 2.0 DATA/handshake packets carry no address or endpoint.
        // Attribute them to the latest token, never their unused VIP fields.
        if (!(pkt.pid_name === svt_usb_packet::SOF) &&
            ((pkt.pid_type === svt_usb_packet::TOKEN) ||
             (pkt.pid_type === svt_usb_packet::EXT_TOKEN) ||
             ((pkt.pid_type === svt_usb_packet::SPECIAL) &&
              (pkt.pid_name === svt_usb_packet::PING)))) begin
            token_target_valid = (direction === PACKET_TX);
            token_address = pkt.get_device_address_val();
            token_endpoint = pkt.ept_num;
        end
        record.target_valid = token_target_valid &&
                              !(pkt.pid_name === svt_usb_packet::SOF);
        record.device_address = token_address;
        record.endpoint_number = token_endpoint;
        record.data_length = pkt.get_payload_byte_count();
        record.retry_number = pkt.current_retry_number();
        record.observed_at = $realtime;
        // Documented svt_usb_packet exception APIs, including injected errors.
        // False means no such exception reported, NOT proof of a checked CRC.
        record.crc_error_detected = pkt.crc_error_detected(1'b1);
        record.data_error_detected = pkt.data_error_detected(1'b1);
        if (diagnostics_enabled &&
            (record.crc_error_detected || record.data_error_detected))
            corrupted_packets++;

        // One semantic tracker serves both the retrospective and live APIs.
        // SOF is transparent; every other competing packet cancels the pair.
        if (!(pkt.pid_name === svt_usb_packet::SOF)) begin
            if ((direction === PACKET_TX) &&
                (pkt.pid_type === svt_usb_packet::TOKEN) &&
                (pkt.pid_name === svt_usb_packet::SETUP) &&
                !record.crc_error_detected && !record.data_error_detected) begin
                pending_setup_token = 1'b1;
                pending_setup_data = 1'b0;
            end else if (pending_setup_token && !pending_setup_data &&
                         (direction === PACKET_TX) &&
                         (pkt.pid_type === svt_usb_packet::DATA) &&
                         (pkt.pid_name === svt_usb_packet::DATA0) &&
                         (pkt.get_payload_byte_count() == 8) &&
                         !record.crc_error_detected && !record.data_error_detected) begin
                pending_setup_data = 1'b1;
                record.setup_data = 1'b1;
            end else begin
                record.accepted_setup = pending_setup_data &&
                    (direction === PACKET_RX) &&
                    (pkt.pid_type === svt_usb_packet::HANDSHAKE) &&
                    (pkt.pid_name === svt_usb_packet::ACK) &&
                    !record.crc_error_detected && !record.data_error_detected;
                pending_setup_token = 1'b0;
                pending_setup_data = 1'b0;
            end
        end
        packet_records.push_back(record);
        retained_packet_count++;
        if (record.accepted_setup) begin
            if (setup_ack_trigger_active) begin
                setup_ack_trigger_seen = 1'b1;
                setup_ack_trigger_active = 1'b0;
                setup_ack_observed.trigger();
            end
        end

        if (!stage_trigger_active) begin
            return;
        end
        if ((direction == PACKET_TX) &&
            (pkt.pid_name == svt_usb_packet::SETUP)) begin
            if (target_stage == svt_usb_transfer::SETUP_STAGE) begin
                stage_trigger_active = 1'b0;
                stage_observed.trigger();
            end
            return;
        end
        if (record.accepted_setup && !data_stage_started) begin
            setup_ack_seen = 1'b1;
            return;
        end
        if (setup_ack_seen &&
            (direction == PACKET_TX) &&
            (pkt.pid_name == svt_usb_packet::IN) &&
            !data_stage_started) begin
            data_stage_started = 1'b1;
            if (target_stage == svt_usb_transfer::DATA_STAGE) begin
                stage_trigger_active = 1'b0;
                stage_observed.trigger();
            end
            return;
        end
        if (data_stage_started &&
            (direction == PACKET_RX) &&
            ((pkt.pid_name == svt_usb_packet::DATA0) ||
             (pkt.pid_name == svt_usb_packet::DATA1))) begin
            data_packet_seen = 1'b1;
            return;
        end
        if (data_packet_seen &&
            (direction == PACKET_TX) &&
            (pkt.pid_name == svt_usb_packet::OUT) &&
            (target_stage == svt_usb_transfer::STATUS_STAGE)) begin
            stage_trigger_active = 1'b0;
            stage_observed.trigger();
        end
    endfunction

    virtual function void usb_20_rx_packet_ended(
        svt_usb_link_monitor link_mon,
        svt_usb_packet pkt);
        record_packet(PACKET_RX, pkt);
    endfunction

    virtual function void usb_20_tx_packet_ended(
        svt_usb_link_monitor link_mon,
        svt_usb_packet pkt);
        record_packet(PACKET_TX, pkt);
    endfunction

endclass

`endif // CALIPTRA_SS_USB_OCP_ARBITER_PACKET_CALLBACK_SV
