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

`ifndef CALIPTRA_SS_USB_SUPERSESSION_CHECKER_SVH
`define CALIPTRA_SS_USB_SUPERSESSION_CHECKER_SVH

// Boundary scoreboard for addressed EP0, single-packet control-IN requests.
// The VIP owns general USB protocol checking. This checker correlates only
// the SETUP, response bytes, ACKs and interruption boundaries of this test.
class caliptra_ss_usb_supersession_checker extends uvm_component;
    `uvm_component_utils(caliptra_ss_usb_supersession_checker)
    typedef enum {NO_TOKEN, SETUP_TOKEN, IN_TOKEN, OUT_TOKEN, PING_TOKEN} token_e;
    caliptra_ss_usb_supersession_packet_callback packet_callback;
    caliptra_ss_usb_supersession_transfer_subscriber protocol_sub;
    caliptra_ss_usb_supersession_expected_report_catcher expected_report;
    caliptra_ss_usb_supersession_evidence evidence[$];
    logic [63:0] protocol_requests[$];
    logic [6:0] address;
    logic [15:0] generation;
    string mode = "CORE";
    bit active, characterizing, last_window_valid;
    token_e token;
    int errors = 0, windows = 0, accepted_setups = 0, errors_at_arm = 0;
    int observed_tx_packets, observed_rx_packets;
    logic [3:0] scenarios_checked = '0;
    logic [2:0] stale_phases_checked = '0;
    logic [1:0] recoveries_checked = '0;
    int stale_windows = 0, recoveries = 0, malformed_short = 0, malformed_badcrc = 0;
    bit recovery_due, recovery_after_short;
    int char_setup_tokens = 0, char_data0_packets = 0, char_other_tx = 0;
    int char_handshakes = 0, char_acks = 0, char_rx_other = 0;
    svt_usb_transfer fault_transfer;
    svt_usb_packet fault_packet;
    logic [63:0] fault_setup;
    bit fault_short, fault_transmitted;
    realtime fault_end_at;

    // Credit only externally checked transactions. Malformed transmission
    // requires an exclusive serialized VIP frame and bound TX completion;
    // this is not an internal DUT receive-path assertion.
    covergroup positive_cg with function sample(bit original_ocp,
                                               bit data_completed,
                                               bit status_nyet);
        option.per_instance = 1;
        owner: coverpoint original_ocp;
        boundary: coverpoint data_completed;
        status_kind: coverpoint status_nyet;
        owner_boundary: cross owner, boundary;
    endgroup
    covergroup stale_cg with function sample(int phase);
        option.per_instance = 1;
        observed_phase: coverpoint phase {
            bins ocp_bypass = {0};
            bins stale_exposure = {1};
            bins fresh_service = {2};
        }
    endgroup
    covergroup malformed_cg with function sample(bit short_setup, bit ack_seen);
        option.per_instance = 1;
        injection: coverpoint short_setup;
        observed_ack: coverpoint ack_seen;
        outcome: cross injection, observed_ack;
    endgroup
    covergroup recovery_cg with function sample(bit after_short);
        option.per_instance = 1;
        predecessor: coverpoint after_short;
    endgroup

    function new(string name = "caliptra_ss_usb_supersession_checker",
                 uvm_component parent = null);
        super.new(name, parent);
        positive_cg = new();
        stale_cg = new();
        malformed_cg = new();
        recovery_cg = new();
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        packet_callback = caliptra_ss_usb_supersession_packet_callback::type_id::create(
            "packet_callback");
        protocol_sub = caliptra_ss_usb_supersession_transfer_subscriber::type_id::create(
            "protocol_sub", this);
        packet_callback.sink = this;
        protocol_sub.sink = this;
        expected_report =
            caliptra_ss_usb_supersession_expected_report_catcher::type_id::create(
                "expected_report");
        expected_report.sink = this;
    endfunction

    function void ocp_supersession_report_failure(input string message);
        errors++;
        `uvm_error("SUPERSESSION", message)
    endfunction

    static function logic [63:0] ocp_supersession_get_setup_line(input svt_usb_transfer req);
        return {req.setup_data_w_length, req.setup_data_w_index,
                req.setup_data_w_value, req.setup_data_brequest,
                1'(req.setup_data_bmrequesttype_dir),
                2'(req.setup_data_bmrequesttype_type),
                5'(req.setup_data_bmrequesttype_recipient)};
    endfunction

    static function bit ocp_supersession_check_bytes_match(input logic [7:0] actual[$],
                                    input logic [7:0] expected[$]);
        if (actual.size() != expected.size()) return 0;
        foreach (expected[i])
            if (actual[i] !== expected[i]) return 0;
        return 1;
    endfunction

    function void ocp_supersession_configure_window(input logic [15:0] gen, input logic [6:0] addr);
        if (active || expected_report.installed)
            `uvm_fatal("SUPERSESSION", "Overlapping evidence/report windows")
        generation = gen;
        address = addr;
        evidence.delete();
        protocol_requests.delete();
        token = NO_TOKEN;
        observed_tx_packets = 0;
        observed_rx_packets = 0;
        last_window_valid = 0;
        errors_at_arm = errors;
        characterizing = 0;
        active = 1;
    endfunction

    function void ocp_supersession_check_transfer(input svt_usb_transfer transfer);
        if (!active || characterizing || (transfer == null)) return;
        if ((transfer.xfer_type == svt_usb_transfer::CONTROL_TRANSFER) &&
            (transfer.device_address === address) &&
            (transfer.endpoint_number === 0))
            protocol_requests.push_back(ocp_supersession_get_setup_line(transfer));
    endfunction

    function bit ocp_supersession_check_protocol_seen(input logic [63:0] header);
        foreach (protocol_requests[i])
            if (protocol_requests[i] === header) return 1;
        return 0;
    endfunction

    protected function void ocp_supersession_check_observed_payload(input svt_usb_packet packet,
                                         ref logic [7:0] bytes[$]);
        bit [7:0] payload_bytes[];
        int length;
        int unsigned total;
        bytes.delete();
        length = packet.get_payload_byte_count();
        if ((length < 0) || ((length != 0) &&
            ((packet.payload == null) || (packet.payload_offset < 0)))) begin
            ocp_supersession_report_failure("Invalid observed payload descriptor");
            return;
        end
        if (length == 0) return;
        total = packet.payload.get_pack_byte_cnt();
        if ((packet.payload_offset > total) ||
            (length > total - packet.payload_offset)) begin
            ocp_supersession_report_failure("Observed payload extends beyond its descriptor");
            return;
        end
        if (!packet.payload.get_bytes(packet.payload_offset, length, payload_bytes) ||
            (payload_bytes.size() != length)) begin
            ocp_supersession_report_failure("Observed payload bytes are unavailable");
            return;
        end
        foreach (payload_bytes[i]) bytes.push_back(payload_bytes[i]);
    endfunction

    function void ocp_supersession_check_packet(input bit tx, input svt_usb_packet packet);
        caliptra_ss_usb_supersession_evidence item;
        logic [7:0] bytes[$];
        if (!active || (packet == null)) return;
        if (packet.pid_name == svt_usb_packet::SOF) return;
        if (tx) observed_tx_packets++;
        else observed_rx_packets++;
        if (characterizing) begin
            if (tx) begin
                if ((packet.pid_name == svt_usb_packet::SETUP) &&
                    (packet.get_device_address_val() === address) &&
                    (packet.ept_num === 0)) char_setup_tokens++;
                else if ((char_setup_tokens == 1) &&
                         (packet.pid_name == svt_usb_packet::DATA0))
                    char_data0_packets++;
                else char_other_tx++;
            end else if (packet.pid_name inside {svt_usb_packet::ACK,
                         svt_usb_packet::NAK, svt_usb_packet::NYET,
                         svt_usb_packet::STALL}) begin
                char_handshakes++;
                if (packet.pid_name == svt_usb_packet::ACK) char_acks++;
            end else char_rx_other++;
            return;
        end
        if (tx && (packet.pid_name inside {svt_usb_packet::SETUP,
                    svt_usb_packet::IN, svt_usb_packet::OUT, svt_usb_packet::PING})) begin
            token = NO_TOKEN;
            if ((packet.get_device_address_val() !== address) ||
                (packet.ept_num !== 0)) return;
            if (packet.pid_name == svt_usb_packet::SETUP) begin
                item = caliptra_ss_usb_supersession_evidence::type_id::create(
                    $sformatf("setup_%0d", evidence.size()));
                item.generation = generation;
                item.setup_at = $realtime;
                evidence.push_back(item);
                token = SETUP_TOKEN;
            end else if (evidence.size() != 0) begin
                item = evidence[$];
                case (packet.pid_name)
                    svt_usb_packet::IN: begin
                        token = IN_TOKEN;
                        item.in_tokens++;
                        item.data_pending = 0;
                    end
                    svt_usb_packet::OUT: begin
                        token = OUT_TOKEN;
                        item.out_tokens++;
                        if (item.status_starts == 0)
                            item.first_status_start_at = $realtime;
                        item.status_starts++;
                        item.status_data = 0;
                    end
                    svt_usb_packet::PING: begin
                        token = PING_TOKEN;
                        item.ping_tokens++;
                        if (item.status_starts == 0)
                            item.first_status_start_at = $realtime;
                        item.status_starts++;
                    end
                    default: ;
                endcase
            end
            return;
        end
        if (evidence.size() == 0) return;
        item = evidence[$];
        if (!tx && (packet.pid_name == svt_usb_packet::STALL)) item.stalls++;
        case (token)
            SETUP_TOKEN: begin
                if (tx && (packet.pid_name == svt_usb_packet::DATA0)) begin
                    ocp_supersession_check_observed_payload(packet, bytes);
                    item.setup_data = (bytes.size() == 8);
                    if (item.setup_data)
                        foreach (bytes[i]) item.setup_bytes[i*8 +: 8] = bytes[i];
                end else if (!tx && (packet.pid_name == svt_usb_packet::ACK) &&
                             item.setup_data) begin
                    item.setup_acks++;
                    accepted_setups++;
                    item.setup_ack_at = $realtime;
                    token = NO_TOKEN;
                end
            end
            IN_TOKEN: begin
                if (!tx && (packet.pid_name == svt_usb_packet::NAK)) begin
                    item.naks++;
                    item.nak_at = $realtime;
                    token = NO_TOKEN;
                end else if (!tx && (packet.pid_name inside {
                             svt_usb_packet::DATA0, svt_usb_packet::DATA1})) begin
                    item.data_packets++;
                    if (item.first_data_at == 0) item.first_data_at = $realtime;
                    if (packet.pid_name != svt_usb_packet::DATA1)
                        ocp_supersession_report_failure("Single control-IN response did not use DATA1 (USB 2.0 8.5.3)");
                    ocp_supersession_check_observed_payload(packet, item.pending_data);
                    item.data_pending = 1;
                end else if (tx && (packet.pid_name == svt_usb_packet::ACK) &&
                             item.data_pending) begin
                    item.data_acks++;
                    item.data = item.pending_data;
                    item.data_ack_at = $realtime;
                    item.data_pending = 0;
                    token = NO_TOKEN;
                end
            end
            OUT_TOKEN: begin
                if (tx && (packet.pid_name == svt_usb_packet::DATA1) &&
                    (packet.get_payload_byte_count() == 0)) item.status_data = 1;
                else if (!tx && item.status_data &&
                         ((packet.pid_name == svt_usb_packet::ACK) ||
                          ((packet.pid_name == svt_usb_packet::NYET) &&
                           (packet.speed == svt_usb_types::HS)))) begin
                    // USB 2.0 8.5.1: NYET accepts this OUT/DATA1 ZLP.
                    if (packet.pid_name == svt_usb_packet::ACK) item.status_acks++;
                    else item.status_nyets++;
                    item.status_complete_at = $realtime;
                    item.status_data = 0;
                    token = NO_TOKEN;
                end else if (!tx && (packet.pid_name inside {
                             svt_usb_packet::NAK, svt_usb_packet::STALL}))
                    token = NO_TOKEN;
            end
            PING_TOKEN: begin
                // A PING ACK grants capacity, never completes STATUS.
                if (!tx && (packet.pid_name == svt_usb_packet::ACK)) item.ping_acks++;
                if (!tx) token = NO_TOKEN;
            end
            default: ;
        endcase
    endfunction

    task ocp_supersession_wait_evidence(input int index, input bit nak, input time timeout);
        bit found;
        found = 0;
        fork : bounded_evidence
            begin
                wait (evidence.size() > index);
                if (nak) wait (evidence[index].naks > 0);
                else wait (evidence[index].setup_acks > 0);
                found = 1;
            end
            #(timeout);
        join_any
        disable bounded_evidence;
        if (!found)
            `uvm_fatal("SUPERSESSION", $sformatf(
                "Evidence timeout gen=%0d index=%0d NAK=%0b records=%0d TX/RX=%0d/%0d token=%s protocol=%0d",
                generation, index, nak, evidence.size(), observed_tx_packets,
                observed_rx_packets, token.name(), protocol_requests.size()))
    endtask

    function void ocp_supersession_check_held(input int index);
        if ((evidence.size() <= index) || (evidence[index].naks == 0) ||
            (evidence[index].data_packets != 0))
            ocp_supersession_report_failure("Held legacy request must NAK before any response DATA");
    endfunction

    function void ocp_supersession_check_release(input int index);
        ocp_supersession_check_held(index);
        if (evidence.size() <= index) return;
        evidence[index].released = 1;
        evidence[index].release_at = $realtime;
    endfunction

    // The production predicate is also exercised by the synthetic negative
    // selftest. No intended scenario label can make incorrect evidence pass.
    static function bit ocp_supersession_check_request_matches(
        input caliptra_ss_usb_supersession_evidence item,
        input logic [63:0] header, input bit complete, input bit data_completed,
        input logic [7:0] expected_data[$]);
        if (item == null) return 0;
        if (!item.setup_data || (item.setup_bytes !== header) ||
            (item.setup_acks !== 1) || (item.stalls !== 0) ||
            (item.data_acks !== int'(data_completed)) ||
            (item.data_packets !== int'(data_completed)) ||
            (item.ocp_supersession_get_status_completions() !== int'(complete))) return 0;
        if (!complete && ((item.out_tokens !== 0) ||
                          (item.ping_tokens !== 0) || (item.status_starts !== 0))) return 0;
        if (complete && ((item.out_tokens == 0) || (item.status_starts == 0))) return 0;
        if ((item.setup_ack_at <= 0) || (item.setup_ack_at < item.setup_at)) return 0;
        if (data_completed && ((item.first_data_at < item.setup_ack_at) ||
                              (item.data_ack_at < item.first_data_at))) return 0;
        if (complete && ((item.first_status_start_at < item.data_ack_at) ||
                         (item.status_complete_at < item.first_status_start_at))) return 0;
        if (data_completed && !ocp_supersession_check_bytes_match(item.data, expected_data)) return 0;
        if (item.released && ((item.naks == 0) ||
            (item.first_data_at < item.release_at))) return 0;
        return 1;
    endfunction

    function bit ocp_supersession_check_evidence(input caliptra_ss_usb_supersession_evidence item,
        input logic [63:0] header, input bit complete, input bit data_completed,
        input logic [7:0] expected_data[$]);
        if (!ocp_supersession_check_request_matches(item, header, complete, data_completed, expected_data)) begin
            `uvm_error("SUPERSESSION_COMPARE", "Observed SETUP/stage/length/payload differs from expectation")
            return 0;
        end
        return 1;
    endfunction

    task ocp_supersession_check_request(input int index, input svt_usb_transfer req,
        input bit complete, input bit data_completed,
        input logic [7:0] expected_data[$], input time timeout = 20us);
        caliptra_ss_usb_supersession_evidence item;
        bit seen;
        if (evidence.size() <= index) begin
            ocp_supersession_report_failure("Missing observed SETUP");
            return;
        end
        item = evidence[index];
        seen = 0;
        fork : bounded_protocol
            begin
                while (!ocp_supersession_check_protocol_seen(ocp_supersession_get_setup_line(req))) #1ns;
                seen = 1;
            end
            #(timeout);
        join_any
        disable bounded_protocol;
        item.checked = 1;
        item.valid = ocp_supersession_check_evidence(item, ocp_supersession_get_setup_line(req), complete,
                                      data_completed, expected_data);
        if (!item.valid) errors++;
        if (!seen) begin
            ocp_supersession_report_failure("No corresponding protocol-monitor transfer observation");
            item.valid = 0;
        end
        `uvm_info("SUPERSESSION_WIRE", $sformatf(
            "gen=%0d request=%0d setup=%016h ACK=%0d DATA=%0d/%0d bytes=%0d OUT=%0d PING=%0d STATUS_ACK/NYET=%0d/%0d NAK=%0d valid=%b",
            generation, index, item.setup_bytes, item.setup_acks,
            item.data_packets, item.data_acks, item.data.size(), item.out_tokens,
            item.ping_tokens, item.status_acks, item.status_nyets, item.naks,
            item.valid), UVM_NONE)
    endtask

    function void ocp_supersession_check_window(input int expected_setups);
        last_window_valid = (evidence.size() == expected_setups) &&
                            (errors == errors_at_arm);
        if (evidence.size() != expected_setups)
            ocp_supersession_report_failure("Unexpected observed SETUP/retry count");
        foreach (evidence[i])
            if (!evidence[i].checked || !evidence[i].valid) last_window_valid = 0;
        active = 0;
        if (last_window_valid) windows++;
    endfunction

    function void ocp_supersession_check_positive_coverage();
        int index;
        if (!last_window_valid || (evidence.size() != 2)) return;
        if (evidence[0].ocp_supersession_check_is_ocp() == evidence[1].ocp_supersession_check_is_ocp()) begin
            ocp_supersession_report_failure("Positive window does not switch observed owners");
            return;
        end
        index = 2 * int'(evidence[0].data_acks == 1) + int'(evidence[0].ocp_supersession_check_is_ocp());
        scenarios_checked[index] = 1;
        positive_cg.sample(evidence[0].ocp_supersession_check_is_ocp(), evidence[0].data_acks == 1,
                           evidence[1].status_nyets != 0);
    endfunction

    function void ocp_supersession_check_stale_coverage(input logic [7:0] stale_data[$],
                               input logic [7:0] fresh_data[$]);
        int phase;
        if (!last_window_valid) return;
        phase = -1;
        if ((evidence.size() == 2) && !evidence[0].ocp_supersession_check_is_ocp() &&
            evidence[1].ocp_supersession_check_is_ocp()) phase = 0;
        else if ((evidence.size() == 1) && !evidence[0].ocp_supersession_check_is_ocp()) begin
            if (ocp_supersession_check_bytes_match(evidence[0].data, stale_data)) phase = 1;
            else if (ocp_supersession_check_bytes_match(evidence[0].data, fresh_data)) phase = 2;
        end
        if (phase < 0) begin
            ocp_supersession_report_failure("No observed bypass/stale/fresh signature for negative coverage");
            return;
        end
        stale_phases_checked[phase] = 1;
        stale_windows++;
        stale_cg.sample(phase);
    endfunction

    function void ocp_supersession_check_recovery_coverage();
        if (!last_window_valid || !recovery_due || (evidence.size() != 1) ||
            evidence[0].ocp_supersession_check_is_ocp()) return;
        recoveries++;
        recoveries_checked[int'(recovery_after_short)] = 1;
        recovery_cg.sample(recovery_after_short);
        recovery_due = 0;
    endfunction

    function void ocp_supersession_configure_characterization(input logic [15:0] gen,
                                         input logic [6:0] addr);
        if (recovery_due)
            `uvm_fatal("SUPERSESSION", "New malformed injection before checked valid recovery")
        ocp_supersession_configure_window(gen, addr);
        characterizing = 1;
        char_setup_tokens = 0;
        char_data0_packets = 0;
        char_other_tx = 0;
        char_handshakes = 0;
        char_acks = 0;
        char_rx_other = 0;
        fault_transmitted = 0;
        fault_transfer = null;
        fault_packet = null;
    endfunction

    function bit ocp_supersession_check_characterizing_generation(input logic [15:0] gen);
        return active && characterizing && (generation === gen);
    endfunction

    function void ocp_supersession_configure_fault(input logic [15:0] gen, input svt_usb_transfer transfer,
                             input svt_usb_packet packet, input bit shorten);
        if (!ocp_supersession_check_characterizing_generation(gen) || (fault_transfer != null) ||
            (transfer == null) || (packet == null))
            `uvm_fatal("SUPERSESSION_FAULT", "Invalid serialized fault context")
        fault_transfer = transfer;
        fault_packet = packet;
        fault_setup = ocp_supersession_get_setup_line(transfer);
        fault_short = shorten;
    endfunction

    function void ocp_supersession_check_fault_transmitted(input svt_usb_transfer transfer,
        input svt_usb_packet packet, input realtime ended_at);
        if ((transfer != fault_transfer) || (packet != fault_packet) ||
            (ended_at <= 0) || (ended_at > $realtime) ||
            (char_setup_tokens != 1) || (char_data0_packets != 1))
            `uvm_fatal("SUPERSESSION_FAULT", "Missing bound SETUP packet transmission completion")
        fault_transmitted = 1;
        fault_end_at = ended_at;
    endfunction

    function bit ocp_supersession_check_badcrc_silence_context(input svt_usb_transfer transfer,
                                       input svt_usb_packet packet);
        return active && characterizing && !fault_short && fault_transmitted &&
               (transfer == fault_transfer) && (packet == fault_packet) &&
               (ocp_supersession_get_setup_line(transfer) === fault_setup) &&
               (char_setup_tokens == 1) && (char_data0_packets == 1) &&
               (char_other_tx == 0) && (char_handshakes == 0) && (char_rx_other == 0);
    endfunction

    // USB 2.0 8.1, 8.3.5.2: LSB-first data, all-ones seed, complemented
    // remainder. A001 is the reflected form of x^16 + x^15 + x^2 + 1.
    static function logic [15:0] ocp_supersession_get_setup_crc16(input logic [63:0] setup_bytes,
                                           input int byte_count);
        localparam logic [15:0] CRC16_REFLECTED_POLYNOMIAL = 16'hA001;
        logic [15:0] crc;
        crc = '1;
        for (int i = 0; i < byte_count * 8; i++) begin
            if (crc[0] ^ setup_bytes[i])
                crc = (crc >> 1) ^ CRC16_REFLECTED_POLYNOMIAL;
            else crc >>= 1;
        end
        return ~crc;
    endfunction

    static function bit ocp_supersession_check_fault_wire_matches(input logic [7:0] tx_bytes[$],
        input logic [63:0] setup_bytes, input bit shorten);
        // USB 2.0 Table 8-1 and 8.4.3: DATA0 PID, data, CRC16.
        localparam logic [7:0] DATA0_PID = 8'hC3;
        int byte_count;
        logic [15:0] expected_crc;
        byte_count = shorten ? 4 : 8;
        if (tx_bytes.size() != byte_count + 3) return 0;
        if (tx_bytes[0] !== DATA0_PID) return 0;
        for (int i = 0; i < byte_count; i++)
            if (tx_bytes[i + 1] !== setup_bytes[i*8 +: 8]) return 0;
        expected_crc = ocp_supersession_get_setup_crc16(setup_bytes, byte_count) ^
                       (shorten ? 16'h0000 : 16'h0001);
        return {tx_bytes[byte_count + 2], tx_bytes[byte_count + 1]} === expected_crc;
    endfunction

    function void ocp_supersession_check_characterization(input int bindings, input int injections,
        input logic [7:0] tx_bytes[$], input bit tx_framed);
        bit valid;
        valid = fault_transmitted && (bindings == 1) && (injections == 1) &&
                (char_setup_tokens == 1) && (char_data0_packets == 1) &&
                (char_other_tx == 0) && tx_framed &&
                ocp_supersession_check_fault_wire_matches(tx_bytes, fault_setup, fault_short);
        if (!fault_short) begin
            valid &= (char_handshakes == 0) && (char_rx_other == 0) &&
                     (expected_report.matched_reports == 1);
        end
        if (!valid) ocp_supersession_report_failure("Malformed SETUP binding/transmission/silence evidence mismatch");
        else begin
            if (fault_short) malformed_short++;
            else malformed_badcrc++;
            malformed_cg.sample(fault_short, char_acks != 0);
        end
        recovery_due = valid;
        recovery_after_short = fault_short;
        `uvm_info("SUPERSESSION_MALFORMED", $sformatf(
            "gen=%0d short=%b txFramed=%b serializedBytes=%p boundTXend=%0t handshakes=%0d otherRX=%0d valid=%b",
            generation, fault_short, tx_framed, tx_bytes,
            fault_end_at, char_handshakes, char_rx_other, valid), UVM_NONE)
        active = 0;
        characterizing = 0;
        fault_transfer = null;
        fault_packet = null;
    endfunction

    // Synchronous and outside live traffic. The catcher is attached to this
    // reporter only, and removed before any actual USB evidence is collected.
    function void ocp_supersession_check_negative_selftest();
        caliptra_ss_usb_supersession_evidence item;
        caliptra_ss_usb_supersession_selftest_catcher catcher;
        logic [7:0] expected[$];
        logic [7:0] malformed_bytes[$];
        bit payload_rejected, stage_rejected;
        if (active) `uvm_fatal("SUPERSESSION_SELFTEST", "Selftest during live traffic")
        malformed_bytes = '{8'hC3, 8'h80, 8'h06, 8'h00, 8'h01, 8'hF7, 8'hDA};
        if (!ocp_supersession_check_fault_wire_matches(malformed_bytes, 64'h0012_0000_0100_0680, 1))
            `uvm_fatal("SUPERSESSION_SELFTEST", "Valid short SETUP wire image rejected")
        malformed_bytes[5] ^= 8'h01;
        if (ocp_supersession_check_fault_wire_matches(malformed_bytes, 64'h0012_0000_0100_0680, 1))
            `uvm_fatal("SUPERSESSION_SELFTEST", "Corrupt short SETUP CRC accepted")
        malformed_bytes = '{8'hC3, 8'h80, 8'h06, 8'h00, 8'h01, 8'h00,
                            8'h00, 8'h12, 8'h00, 8'hE1, 8'hF4};
        if (!ocp_supersession_check_fault_wire_matches(malformed_bytes, 64'h0012_0000_0100_0680, 0))
            `uvm_fatal("SUPERSESSION_SELFTEST", "Expected badCRC SETUP wire image rejected")
        malformed_bytes[9] ^= 8'h01;
        if (ocp_supersession_check_fault_wire_matches(malformed_bytes, 64'h0012_0000_0100_0680, 0))
            `uvm_fatal("SUPERSESSION_SELFTEST", "Clean SETUP accepted as badCRC injection")
        void'(malformed_bytes.pop_back());
        if (ocp_supersession_check_fault_wire_matches(malformed_bytes, 64'h0012_0000_0100_0680, 0))
            `uvm_fatal("SUPERSESSION_SELFTEST", "Truncated badCRC wire image accepted")
        item = caliptra_ss_usb_supersession_evidence::type_id::create("synthetic");
        catcher = caliptra_ss_usb_supersession_selftest_catcher::type_id::create("local_errors");
        expected = '{8'h12, 8'h01};
        item.setup_data = 1;
        item.setup_bytes = 64'h0002_0000_0100_0680;
        item.setup_acks = 1;
        item.data_packets = 1;
        item.data_acks = 1;
        item.out_tokens = 1;
        item.status_starts = 1;
        item.status_acks = 1;
        item.setup_at = 1;
        item.setup_ack_at = 2;
        item.first_data_at = 3;
        item.data_ack_at = 4;
        item.first_status_start_at = 5;
        item.status_complete_at = 6;
        item.data = expected;
        if (!ocp_supersession_check_request_matches(item, item.setup_bytes, 1, 1, expected))
            `uvm_fatal("SUPERSESSION_SELFTEST", "Synthetic positive control rejected")
        catcher.client = this;
        catcher.armed = 1;
        uvm_report_cb::add(this, catcher);
        item.data[0] ^= 8'h01;
        payload_rejected = !ocp_supersession_check_evidence(item, item.setup_bytes, 1, 1, expected);
        item.data = expected;
        stage_rejected = !ocp_supersession_check_evidence(item, item.setup_bytes, 0, 0, expected);
        catcher.armed = 0;
        uvm_report_cb::delete(this, catcher);
        if (!payload_rejected || !stage_rejected || (catcher.match_count !== 2))
            `uvm_fatal("SUPERSESSION_SELFTEST", "Production predicate failed negative payload/stage selftest")
        `uvm_info("SUPERSESSION_SELFTEST", "Payload/stage and malformed-frame selftests passed", UVM_NONE)
    endfunction

    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        if (active || expected_report.installed || expected_report.armed)
            ocp_supersession_report_failure("Unclosed evidence/report window");
        if ((mode == "CORE") && (scenarios_checked !== 4'hF))
            ocp_supersession_report_failure("Missing observed four-way supersession coverage");
        if ((mode == "STALE") &&
            ((stale_windows != 3) || (stale_phases_checked !== 3'b111)))
            ocp_supersession_report_failure("Missing OCP bypass/stale exposure/fresh service evidence");
        if ((mode == "MALFORMED") &&
            ((malformed_short != 1) || (malformed_badcrc != 1) ||
             (recoveries != 2) || (recoveries_checked !== 2'b11) || recovery_due))
            ocp_supersession_report_failure("Missing separate malformed/recovery evidence");
        if (errors != 0)
            `uvm_error("SUPERSESSION_SUMMARY", $sformatf("%0d boundary checking failures", errors))
    endfunction
endclass
`endif
