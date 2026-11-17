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
// Isolated public-interface arbiter fixture. No subsystem signals or storage
// are driven. USB 2.0 8.5.1/8.5.3 define accepted DATA and control stages;
// the local emergency contract purges only not-yet-published RX words.
// The destination queue is an independent sink, not CMS storage. The real
// decoder is absent and ctrl_set_stall is tied low. Bus/local reset cases
// check public reset outputs only; explicit CMS FIFO reset is not an input.
module caliptra_ss_usb_ocp_rx_drain_unit #(
    parameter int unsigned CLOCK_PERIOD_PS = 2500,
    parameter int unsigned CLOCK_MHZ = 400,
    parameter int unsigned MIN_CLOCK_PERIOD_PS = 16666
) (caliptra_ss_usb_ocp_rx_drain_unit_if vif);
    timeunit 1ps;
    timeprecision 1ps;
    import uvm_pkg::*;
    import caliptra_ss_usb_ocp_recovery_tb_pkg::*;
    import usb_ocp_post_sync_arb_unit_pkg::*;
    `include "uvm_macros.svh"

    localparam int unsigned LOCAL_PROFILE_BYTES = 64;
    localparam int unsigned LOCAL_PROFILE_DWORDS = 16;
    localparam int unsigned LOCAL_FIFO_PURGE_PREFIX_DWORDS = 5;
    localparam int unsigned LOCAL_NONFIFO_BYTES = OCP_SPEC_LEN_INDIRECT_FIFO_CTRL;
    localparam int unsigned LOCAL_NONFIFO_DWORDS = (LOCAL_NONFIFO_BYTES + 3) / 4;
    localparam int unsigned LOCAL_NONFIFO_PURGE_PREFIX_DWORDS = 1;
    localparam int unsigned LOCAL_SHORT_REG_DWORDS = (OCP_SPEC_LEN_RECOVERY_CTRL + 3) / 4;
    localparam logic [1:0] LOCAL_DEV0_SELECTOR = 2'b01;
    localparam int unsigned POLL_CYCLES = 256;
    localparam int unsigned LOCAL_SETUP_BODY_MIN_CLOCK_CYCLES = 27;
    // The early token is synthetic block stimulus, not legal-wire spacing
    // proof. The full body is delayed by at least 27 minimum-clock cycles.
    // Destination handshakes, not this interval, establish drain completion.
    localparam time LOCAL_SETUP_BODY_SEPARATION =
        time'(LOCAL_SETUP_BODY_MIN_CLOCK_CYCLES * MIN_CLOCK_PERIOD_PS);

    logic clk = 0;
    logic reset_n = 0;
    logic bus_reset = 0, local_port_reset = 0, connected = 1;
    logic forwarded_setup_received;
    logic usbreg_setup = 0, dma_setup;
    logic req = 0, dir_in = 0, setup_token = 0, setup_received = 0;
    logic [3:0] epnr = 0;
    logic [11:0] rx_bytes = 0;
    logic [63:0] rx_data = 0;
    logic rx_valid = 0, end_transfer = 0, success = 0, sent_nak = 0;
    logic dma_valid = 0;
    logic ready = 0, claim_abort = 0;
    logic ep_valid, ep_active, ep_stall;
    logic setup_valid, setup_owner, decoder_abort, length_error;
    logic [63:0] published_setup;
    logic [63:0] observed_setup;
    logic [31:0] out_data;
    logic out_valid, out_last, reserved, fifo_reset, batch_abort;
    logic [6:0] free_dwords = 7'(LOCAL_PROFILE_DWORDS);
    logic fifo_command = 0;
    logic event_armed = 0, expected_batch_abort = 0, expected_decoder_abort = 0;
    logic check_sink = 0, permit_data = 0, protect_drain = 0;
    logic arm_fifo_bound = 0, fifo_bound_active = 0;
    int unsigned sink_cycle = 0, acceptance_cycle = 0;
    int unsigned words_seen = 0, expected_words = 0, request_words = 0;
    int unsigned payload_bytes = 0, seed = 0, setup_count = 0, abort_count = 0;
    int unsigned acceptance_abort_count = 0;
    logic [31:0] destination[$];
    string label;
    time early_setup_time;
    // Independent RX eligibility and sink progress, never DUT state/good/valid.
    int unsigned captured_beats = 0, last_push_cycle = 0;
    logic model_accepted = 0, model_has_command = 0;
    logic previous_emergency = 0, previous_physical = 0;
    int unsigned lifecycle_hits[PH_COUNT][EV_COUNT];
    int unsigned acceptance_emergency_hits = 0;
    int unsigned reset_priority_hits[2][3][2];
    lifecycle_t observed_phase;
    event_t observed_event;

    always #(CLOCK_PERIOD_PS / 2) clk = ~clk;
    assign vif.clk = clk;
    assign vif.clock_mhz = CLOCK_MHZ;
    assign vif.reset_n = reset_n;
    assign vif.out_valid = out_valid;
    assign vif.out_ready = ready;
    assign vif.out_data = out_data;
    assign vif.out_last = out_last;
    assign vif.emergency_abort = claim_abort;
    assign vif.reservation = reserved;
    assign vif.physical_fifo_reset = fifo_reset;
    assign vif.fifo_batch_abort = batch_abort;
    assign vif.ctrl_xfer_abort = decoder_abort;
    assign vif.expected_physical_reset_window = bus_reset || local_port_reset || !connected;
    assign vif.setup_received = setup_received;
    assign vif.forwarded_setup_received = forwarded_setup_received;

    // Only port declarations determine widths/directions here. All expected
    // words and purge limits are independently chosen by this fixture.
    usb_ocp_recovery_post_sync_arb #(
        .USB_DATAWIDTH(64), .RXNBYTES_BITS(12), .TXNBYTES_BITS(15),
        .C_REC_IFACE_NUM(0)
    ) arbiter (
        .hclk(clk),
        .hresetn(reset_n),
        .sync_busreset(bus_reset),
        .pie_dev_selected_i(LOCAL_DEV0_SELECTOR),
        .dev0_port_reset_i(local_port_reset),
        .dev0_usbreg_dev_connect_i(connected),
        .usbreg_setup_i(usbreg_setup),
        .usbreg_setup_dma_o(dma_setup),
        .sync_sieint_epinfo_req_i(req),
        .sync_sieint_epinfo_epnr_i(epnr),
        .sync_sieint_epinfo_epdir_i(dir_in),
        .sync_sieint_epinfo_setup_i(setup_token),
        .sync_sieint_setup_received_i(setup_received),
        .sync_sieint_rx_nbytes_i(rx_bytes),
        .sync_sieint_rxdata_i(rx_data),
        .sync_sieint_rxdatavalid_i(rx_valid),
        .sync_sieint_endtransfer_i(end_transfer),
        .sync_sieint_success_i(success),
        .sync_sieint_error_i(1'b0),
        .sync_sieint_errortype_i(4'b0),
        .sync_sieint_sentNAK_i(sent_nak),
        .sync_sieint_txdatafetched_i(1'b0),
        .epinfo_sync_valid_dma(dma_valid),
        .epinfo_sync_active_dma(1'b1),
        .epinfo_sync_disabled_dma(1'b0),
        .epinfo_sync_toggle_dma(1'b0),
        .epinfo_sync_stall_dma(1'b0),
        .epinfo_sync_iso_dma(1'b0),
        .epinfo_sync_ratefeedbackmode_dma(1'b0),
        .epinfo_sync_nbytes_dma(15'b0),
        .epinfo_sync_maxpacket_dma(2'b00),
        .epinfo_sync_txdata_dma(64'b0),
        .epinfo_sync_txdata_valid_dma(1'b0),
        .sync_sieint_epinfo_req_o(),
        .sync_sieint_epinfo_epnr_o(),
        .sync_sieint_epinfo_epdir_o(),
        .sync_sieint_epinfo_setup_o(),
        .sync_sieint_rx_nbytes_o(),
        .sync_sieint_rxdata_o(),
        .sync_sieint_rxdatavalid_o(),
        .sync_sieint_endtransfer_o(),
        .sync_sieint_success_o(),
        .sync_sieint_sentNAK_o(),
        .sync_sieint_txdatafetched_o(),
        .sync_sieint_setup_received_o(forwarded_setup_received),
        .sync_sieint_error_o(),
        .sync_sieint_errortype_o(),
        .epinfo_sync_valid_o(ep_valid),
        .epinfo_sync_active_o(ep_active),
        .epinfo_sync_disabled_o(),
        .epinfo_sync_toggle_o(),
        .epinfo_sync_stall_o(ep_stall),
        .epinfo_sync_iso_o(),
        .epinfo_sync_ratefeedbackmode_o(),
        .epinfo_sync_nbytes_o(),
        .epinfo_sync_maxpacket_o(),
        .epinfo_sync_txdata_o(),
        .epinfo_sync_txdata_valid_o(),
        .setup_pkt_vld(setup_valid),
        .setup_pkt(published_setup),
        .setup_generation_o(),
        .setup_owner_ocp_o(setup_owner),
        .post_sync_arb_state_o(),
        .ctrl_out_data(out_data),
        .ctrl_out_vld(out_valid),
        .ctrl_out_last(out_last),
        .ctrl_out_rdy(ready),
        .ctrl_in_data(32'b0),
        .ctrl_in_be(4'hF),
        .ctrl_in_vld(1'b0),
        .ctrl_in_last(1'b0),
        .ctrl_in_rdy(),
        .ctrl_in_resp_bytes(7'(OCP_SPEC_LEN_PROT_CAP)),
        .ctrl_in_resp_known(1'b1),
        .ctrl_set_stall(1'b0),
        .ctrl_xfer_done(),
        .ctrl_xfer_abort(decoder_abort),
        .fifo_batch_abort(batch_abort),
        .fifo_batch_reset(fifo_reset),
        .ctrl_length_error(length_error),
        .ocp_path_disable_i(1'b0),
        .ocp_claim_abort_i(claim_abort),
        .fw_protocol_error_req_i(1'b0),
        .fifo_payload_available_i(1'b0),
        .fifo_free_dwords_i(free_dwords),
        .fifo_reservation_active_o(reserved)
    );

    function automatic logic [7:0] chosen_byte(input int unsigned index);
        return 8'(seed ^ index);
    endfunction
    function automatic logic [31:0] chosen_word(input int unsigned index);
        logic [31:0] word_value;
        word_value = 0;
        for (int unsigned b = 0; b < 4; b++)
            if (index * 4 + b < payload_bytes)
                word_value[b * 8 +: 8] = chosen_byte(index * 4 + b);
        return word_value;
    endfunction
    function automatic logic [63:0] chosen_setup(
        input ocp_cmd_t command, input int unsigned bytes, input bit read_request);
        // USB 2.0 9.3 / OCP Recovery v1.1 8.5 class/interface SETUP.
        return {16'(bytes), 16'h0000, 8'h00, command, 8'h00,
                read_request ? 8'hA1 : 8'h21};
    endfunction
    task automatic fail(input string message);
        vif.errors++;
        `uvm_fatal("OCP_RX_DRAIN_UNIT", {label, ": ", message})
    endtask

    // Passive independent destination scoreboard, sampled on public transfer
    // edges. Its history is never cleared by claim-abort or arbiter reset.
    always @(posedge clk) begin
        if (!reset_n) begin
            sink_cycle = 0;
            captured_beats = 0;
            model_accepted = 0;
            model_has_command = 0;
            previous_emergency = 0;
            previous_physical = 0;
        end
        if (reset_n && vif.running) begin
            sink_cycle++;
            // Classify before the current destination edge. In particular an
            // emergency-masked valid cannot be used to prove final/acceptance
            // coincidence. Captured beats and earlier sink transfers can.
            if (request_words != 0 && words_seen == request_words)
                observed_phase = sink_cycle == last_push_cycle + 1 ? PH_TAIL : PH_POSTDONE;
            else if (words_seen != 0)
                observed_phase = words_seen + 1 == request_words ? PH_FINAL : PH_PARTIAL;
            else if (model_accepted ||
                     (captured_beats == (payload_bytes + 7) / 8 &&
                      end_transfer && success && !dir_in && !setup_token &&
                      rx_bytes == payload_bytes))
                observed_phase = PH_ELIGIBLE;
            else if (captured_beats != 0)
                observed_phase = PH_INCOMPLETE;
            else
                observed_phase = PH_PENDING;
            if (!model_has_command) observed_phase = PH_IDLE;
            vif.lifecycle_phase = observed_phase;
            if (bus_reset) observed_event = EV_BUS;
            else if (local_port_reset) observed_event = EV_PORT;
            else if (!connected) observed_event = EV_DISCONNECT;
            else if (claim_abort && !previous_emergency) observed_event = EV_EMERGENCY;
            else observed_event = EV_SETUP;
            if ((req && setup_token) || (claim_abort && !previous_emergency) ||
                ((bus_reset || local_port_reset || !connected) && !previous_physical)) begin
                lifecycle_hits[observed_phase][observed_event]++;
                vif.sample_lifecycle(observed_phase, observed_event);
                if (!previous_physical && (bus_reset || local_port_reset || !connected) &&
                    (observed_phase == PH_PENDING || observed_phase == PH_FINAL)) begin
                    if (req && setup_token)
                        reset_priority_hits[observed_phase == PH_FINAL][int'(observed_event)-int'(EV_BUS)][0]++;
                    if (claim_abort)
                        reset_priority_hits[observed_phase == PH_FINAL][int'(observed_event)-int'(EV_BUS)][1]++;
                end
                if (claim_abort && end_transfer && success && !setup_token &&
                    !dir_in && captured_beats == (payload_bytes + 7) / 8 &&
                    rx_bytes == payload_bytes)
                    acceptance_emergency_hits++;
            end
            previous_emergency = claim_abort;
            previous_physical = bus_reset || local_port_reset || !connected;
            if (setup_valid === 1'b1) begin
                observed_setup = published_setup;
                setup_count++;
                captured_beats = 0;
                model_accepted = 0;
                model_has_command = 1;
            end
            if (decoder_abort === 1'b1) abort_count++;
            if (bus_reset || local_port_reset || !connected) begin
                if (setup_received === 1'b1 && forwarded_setup_received === 1'b1)
                    vif.reset_setup_high_checks++;
                if (out_valid !== 1'b0 || decoder_abort !== 1'b1)
                    fail("Pending-RX reset did not immediately suppress valid/abort decoder.");
                if (batch_abort !== 1'b0 || fifo_reset !== 1'b1)
                    fail("Physical reset must assert reset without batch-abort notification.");
                vif.reset_boundary_checks++;
                `uvm_info("OCP_RX_DRAIN_UNIT",
                    $sformatf("RX_RESET_EVENT %s bus=%b local=%b words=%0d batch=%b physical=%b",
                        label, bus_reset, local_port_reset, words_seen,
                        batch_abort, fifo_reset), UVM_NONE)
            end
            // Sample on the event edge, before sequential cleanup can remove
            // a combinational cancellation pulse.
            if (event_armed) begin
                if (batch_abort !== expected_batch_abort ||
                    decoder_abort !== expected_decoder_abort)
                    fail($sformatf("Event notification batch/decoder=%b/%b expected=%b/%b.",
                        batch_abort, decoder_abort,
                        expected_batch_abort, expected_decoder_abort));
                vif.notification_checks++;
                `uvm_info("OCP_RX_DRAIN_UNIT",
                    $sformatf("RX_EVENT %s batch=%b decoder=%b words=%0d",
                        label, batch_abort, decoder_abort, words_seen), UVM_NONE)
                event_armed = 0;
            end
            if (check_sink) begin
                if (arm_fifo_bound && end_transfer && success && !claim_abort) begin
                    if (fifo_bound_active) fail("Duplicate acceptance-edge cycle check.");
                    acceptance_cycle = sink_cycle;
                    fifo_bound_active = 1;
                end
                if (fifo_bound_active) begin
                    if (sink_cycle == acceptance_cycle) begin
                        if (out_valid === 1'b1 && ready === 1'b1)
                            fail("FIFO published on A instead of first push A+1.");
                    end else begin
                        if (!(out_valid === 1'b1 && ready === 1'b1) ||
                            words_seen != sink_cycle - acceptance_cycle - 1)
                            fail($sformatf("FIFO 16-cycle bound: edge A+%0d words_before=%0d.",
                                sink_cycle - acceptance_cycle, words_seen));
                    end
                end
                if ($isunknown({out_valid, ready}) ||
                    (out_valid === 1'b1 && $isunknown({out_data, out_last})))
                    fail("X/Z on decoder handshake.");
                if (!permit_data && out_valid === 1'b1)
                    fail("RX was exposed without qualified full DATA acceptance.");
                if (protect_drain &&
                    (decoder_abort !== 1'b0 || batch_abort !== 1'b0))
                    fail("Ordinary SETUP aborted an accepted drain/completion tail.");
                if ((out_valid === 1'b1) && (ready === 1'b1)) begin
                    if (words_seen >= expected_words)
                        fail("Extra word published after planned purge/length.");
                    if (out_data !== chosen_word(words_seen))
                        fail($sformatf("word[%0d]=%08h expected=%08h",
                            words_seen, out_data, chosen_word(words_seen)));
                    if (out_last !== (words_seen + 1 == request_words))
                        fail("Incorrect final-word marker or truncated drain.");
                    destination.push_back(out_data);
                    words_seen++;
                    last_push_cycle = sink_cycle;
                    if (fifo_bound_active &&
                        sink_cycle == acceptance_cycle + LOCAL_PROFILE_DWORDS) begin
                        if (words_seen != LOCAL_PROFILE_DWORDS)
                            fail("FIFO final push did not occur at A+16.");
                        fifo_bound_active = 0;
                        vif.fifo_bound_checks++;
                    end
                end
                if (rx_valid && !setup_token) captured_beats++;
                if (end_transfer && success && !dir_in && !setup_token &&
                    captured_beats == (payload_bytes + 7) / 8 && rx_bytes == payload_bytes)
                    model_accepted = 1;
            end
        end
    end

    task automatic tick(input int unsigned cycles = 1);
        repeat (cycles) @(negedge clk);
    endtask
    task automatic arm_notification(input bit batch_expected, input bit decoder_expected);
        if (event_armed) fail("Previous event notification was not sampled.");
        expected_batch_abort = batch_expected;
        expected_decoder_abort = decoder_expected;
        event_armed = 1;
    endtask
    task automatic wait_words(input int unsigned count);
        for (int unsigned n = 0; n < POLL_CYCLES; n++) begin
            if (words_seen == count) return;
            tick();
        end
        fail($sformatf("Bound expired: words=%0d expected=%0d.", words_seen, count));
    endtask
    task automatic check_quiet();
        // A bounded negative observation, not a completion timer.
        tick(32);
        if (words_seen != expected_words) fail("Missing expected destination words.");
    endtask
    task automatic reset_case(input string next_label, input int unsigned bytes,
                              input int unsigned retained_words);
        tick();
        check_sink = 0;
        reset_n = 0;
        bus_reset = 0; local_port_reset = 0; connected = 1;
        req = 0; setup_token = 0; setup_received = 0; dir_in = 0; epnr = 0;
        rx_valid = 0; end_transfer = 0; success = 0; sent_nak = 0;
        dma_valid = 0; ready = 0; claim_abort = 0; permit_data = 0;
        usbreg_setup = 0;
        protect_drain = 0;
        if (event_armed) fail("Unconsumed event expectation at case boundary.");
        free_dwords = 7'(LOCAL_PROFILE_DWORDS);
        fifo_command = 0;
        arm_fifo_bound = 0; fifo_bound_active = 0;
        tick(4);
        label = next_label;
        payload_bytes = bytes;
        request_words = (bytes + 3) / 4;
        expected_words = retained_words;
        words_seen = 0;
        seed = 8'h51 + vif.cases * 7;
        reset_n = 1;
        ready = 1;
        check_sink = 1;
        tick();
    endtask
    task automatic setup_token_request();
        req = 1; dir_in = 0; epnr = 0; setup_token = 1; rx_bytes = 8;
        early_setup_time = $time;
        tick();
        req = 0;
        // Response emulates the public endpoint DMA metadata handshake.
        dma_valid = 1;
        tick();
        dma_valid = 0;
    endtask
    task automatic setup_start();
        tick();
        setup_token_request();
    endtask
    task automatic setup_body(input logic [63:0] packet);
        int unsigned previous_count;
        previous_count = setup_count;
        tick();
        rx_data = packet; rx_bytes = 8; rx_valid = 1;
        tick();
        rx_valid = 0; setup_received = 1; end_transfer = 1; success = 1;
        tick();
        setup_received = 0; end_transfer = 0; success = 0; setup_token = 0;
        for (int unsigned n = 0; n < POLL_CYCLES; n++) begin
            if (setup_count > previous_count) begin
                // Publication data is sampled on its transfer edge; registered
                // ownership is checked here on the following falling edge.
                if (observed_setup !== packet || setup_owner !== 1'b1)
                    fail($sformatf("SETUP=%016h expected=%016h owner=%b.",
                        observed_setup, packet, setup_owner));
                return;
            end
            tick();
        end
        fail("Missing qualified SETUP publication.");
    endtask
    task automatic setup_request(input ocp_cmd_t command,
                                 input int unsigned bytes, input bit read_request = 0);
        fifo_command = command == OCP_CMD_INDIRECT_FIFO_DATA && !read_request;
        setup_start();
        setup_body(chosen_setup(command, bytes, read_request));
    endtask
    task automatic request_stage(input bit read_request = 0, input bit active_expected = 1);
        tick();
        rx_bytes = 12'(payload_bytes);
        dir_in = read_request; setup_token = 0; epnr = 0; req = 1;
        tick();
        for (int unsigned n = 0; n < POLL_CYCLES; n++) begin
            if (ep_valid === 1'b1) begin
                if (ep_stall !== 1'b0 || ep_active !== active_expected)
                    fail($sformatf("Endpoint metadata: stall=%b active=%b expected_active=%b.",
                        ep_stall, ep_active, active_expected));
                req = 0;
                return;
            end
            tick();
        end
        fail("Endpoint metadata handshake timed out.");
    endtask
    task automatic capture_data(input int unsigned beats, input bit final_beat_eop = 0);
        for (int unsigned beat = 0; beat < beats; beat++) begin
            tick();
            rx_data = 0;
            for (int unsigned b = 0; b < 8; b++)
                if (beat * 8 + b < payload_bytes)
                    rx_data[b * 8 +: 8] = chosen_byte(beat * 8 + b);
            rx_bytes = 12'(payload_bytes); rx_valid = 1;
            if (final_beat_eop && beat + 1 == beats) begin
                arm_fifo_bound = 1;
                end_transfer = 1; success = 1; permit_data = 1; ready = 1;
            end
        end
        tick();
        rx_valid = 0;
        if (final_beat_eop) begin
            end_transfer = 0; success = 0;
            arm_fifo_bound = 0;
        end
    endtask
    task automatic accept_data(input bit emergency = 0, input bit rejected = 0,
                               input bit require_fifo_bound = 0);
        acceptance_abort_count = abort_count;
        end_transfer = 1; success = !rejected; sent_nak = rejected;
        claim_abort = emergency; ready = 1;
        if (emergency) arm_notification(fifo_command, 1);
        permit_data = !emergency && !rejected;
        arm_fifo_bound = require_fifo_bound;
        tick();
        end_transfer = 0; success = 0; sent_nak = 0;
        arm_fifo_bound = 0;
    endtask
    task automatic emergency_purge(input bit pending_data = 1);
        int unsigned previous_abort;
        logic [31:0] retained_history[$];
        retained_history = destination;
        previous_abort = claim_abort ? acceptance_abort_count : abort_count;
        if (!claim_abort) arm_notification(fifo_command && pending_data, 1);
        claim_abort = 1;
        tick();
        for (int unsigned n = 0; n < POLL_CYCLES; n++) begin
            if (reserved === 1'b0 && abort_count > previous_abort) begin
                if (destination.size() != retained_history.size())
                    fail("Emergency changed committed sink history size.");
                foreach (retained_history[i])
                    if (destination[i] !== retained_history[i])
                        fail($sformatf("Emergency changed committed sink word %0d.", i));
                claim_abort = 0;
                ready = 1;
                return;
            end
            tick();
        end
        fail("Emergency did not abort decoder/release reservation.");
    endtask
    task automatic check_reservation_released();
        for (int unsigned n = 0; n < POLL_CYCLES; n++) begin
            if (reserved === 1'b0) return;
            tick();
        end
        fail("Canceled/completed command retained its reservation.");
    endtask
    task automatic finish_case();
        check_quiet();
        if (event_armed) fail("Event notification check did not execute.");
        vif.cases++;
        `uvm_info("OCP_RX_DRAIN_UNIT",
            $sformatf("case=%0d %s expected/published=%0d/%0d destination_total=%0d",
                vif.cases, label, expected_words, words_seen, destination.size()), UVM_NONE)
    endtask
    task automatic full_request(input ocp_cmd_t command, input string next_label,
                                input int unsigned keep, input int unsigned bytes = LOCAL_PROFILE_BYTES);
        reset_case(next_label, bytes, keep);
        setup_request(command, bytes);
        request_stage();
        capture_data((bytes + 7) / 8);
    endtask
    task automatic early_setup();
        int unsigned previous_setups;
        ready = 1;
        wait_words(LOCAL_FIFO_PURGE_PREFIX_DWORDS);
        protect_drain = 1;
        previous_setups = setup_count;
        tick();
        arm_notification(0, 0);
        setup_token_request();
        // No full SETUP publication while the original 16-word drain is
        // active. Only its token is supplied early; the body arrives safely.
        while ($time - early_setup_time < LOCAL_SETUP_BODY_SEPARATION) begin
            if (setup_count != previous_setups)
                fail("SETUP published before its eight-byte body was supplied.");
            tick();
        end
        if (setup_count != previous_setups)
            fail("Premature SETUP publication.");
        wait_words(request_words);
        check_reservation_released();
        protect_drain = 0;
        setup_body(chosen_setup(OCP_CMD_RECOVERY_CTRL, OCP_SPEC_LEN_RECOVERY_CTRL, 0));
    endtask
    task automatic zero_data_cancel(input string next_label,
                                    input int unsigned capacity, input bit emergency);
        reset_case(next_label, LOCAL_PROFILE_BYTES, 0);
        free_dwords = 7'(capacity);
        setup_request(OCP_CMD_INDIRECT_FIFO_DATA, LOCAL_PROFILE_BYTES);
        request_stage(0, capacity >= LOCAL_PROFILE_DWORDS);
        // A legal nonzero wLength has been published, but no DATA beat has
        // arrived. Capacity affects reservation, never cancellation notice.
        // This does not claim unpublished META coverage from an incomplete
        // SETUP body: cancellation before SETUP EOP is a different boundary.
        if (reserved !== (capacity >= LOCAL_PROFILE_DWORDS))
            fail("Zero-DATA reservation did not match available capacity.");
        if (emergency) begin
            emergency_purge();
        end else begin
            arm_notification(1, 1);
            setup_token_request();
            check_reservation_released();
        end
        finish_case();
    endtask
    task automatic finish_replacement_setup();
        // Keep the replacement body outside the accepted drain/completion
        // interval even when its token deliberately overlaps that interval.
        while ($time - early_setup_time < LOCAL_SETUP_BODY_SEPARATION) tick();
        setup_body(chosen_setup(OCP_CMD_RECOVERY_CTRL, OCP_SPEC_LEN_RECOVERY_CTRL, 0));
    endtask
    task automatic reset_pending_rx(input string next_label, input bit bus_event);
        logic [31:0] published_history[$];
        full_request(OCP_CMD_INDIRECT_FIFO_DATA, next_label,
            LOCAL_FIFO_PURGE_PREFIX_DWORDS);
        accept_data(); wait_words(LOCAL_FIFO_PURGE_PREFIX_DWORDS);
        published_history = destination;
        // Drive at the falling edge immediately after push five. This avoids
        // the final-push/completion-tail reset-policy boundary.
        permit_data = 0;
        bus_reset = bus_event;
        local_port_reset = !bus_event;
        tick();
        if (reserved !== 1'b0)
            fail("Pending-RX reset did not release its reservation.");
        bus_reset = 0; local_port_reset = 0;
        // Stale DATA and a late successful EOP must not revive the reset RX
        // candidate. No fresh endpoint request or SETUP is supplied.
        capture_data(3);
        end_transfer = 1; success = 1;
        tick(); end_transfer = 0; success = 0;
        finish_case();
        // Publication history is not a model of destructive CMS reset scope.
        if (destination.size() != published_history.size())
            fail("Reset RX published beyond its expected five-word history.");
        foreach (published_history[i])
            if (destination[i] !== published_history[i])
                fail($sformatf("Reset changed publication history word %0d.", i));
    endtask
    // USB 2.0 8.5.3 control supersession and the local accepted-payload
    // retention/emergency/physical-reset contract are checked independently.
    // The sink count selects a lifecycle boundary; no specific prefix length
    // is a coverage bin.
    task automatic lifecycle_case(input lifecycle_t phase_id, input event_t event_id,
                                  input int unsigned collision = 0);
        int unsigned keep, before_hits;
        bit preserve;
        preserve = event_id == EV_SETUP &&
                   phase_id >= PH_ELIGIBLE && phase_id <= PH_POSTDONE;
        keep = 0;
        if (preserve || phase_id == PH_TAIL || phase_id == PH_POSTDONE)
            keep = LOCAL_PROFILE_DWORDS;
        else if (phase_id == PH_PARTIAL) keep = LOCAL_PROFILE_DWORDS / 2;
        else if (phase_id == PH_FINAL) keep = LOCAL_PROFILE_DWORDS - 1;
        reset_case($sformatf("LIFECYCLE_%s_%s_collision%0d",
            phase_id.name(), event_id.name(), collision), LOCAL_PROFILE_BYTES, keep);
        if (phase_id != PH_IDLE) begin
            setup_request(OCP_CMD_INDIRECT_FIFO_DATA, LOCAL_PROFILE_BYTES);
            if (phase_id != PH_PENDING) begin
                request_stage();
                if (phase_id == PH_INCOMPLETE) capture_data(3);
                else begin
                    capture_data(LOCAL_PROFILE_BYTES / 8);
                    accept_data();
                    case (phase_id)
                        PH_PARTIAL: wait_words(LOCAL_PROFILE_DWORDS / 2);
                        PH_FINAL: wait_words(LOCAL_PROFILE_DWORDS - 1);
                        PH_TAIL: wait_words(LOCAL_PROFILE_DWORDS);
                        PH_POSTDONE: begin wait_words(LOCAL_PROFILE_DWORDS); tick(4); end
                        default: ;
                    endcase
                end
            end
        end
        before_hits = lifecycle_hits[phase_id][event_id];
        if (event_id == EV_SETUP) begin
            protect_drain = preserve && phase_id != PH_POSTDONE;
            arm_notification(phase_id <= PH_INCOMPLETE,
                             phase_id <= PH_INCOMPLETE || phase_id == PH_POSTDONE);
            setup_token_request();
            if (preserve) wait_words(LOCAL_PROFILE_DWORDS);
            check_reservation_released();
            protect_drain = 0;
            finish_replacement_setup();
        end else if (event_id == EV_EMERGENCY) begin
            permit_data = 0;
            emergency_purge(phase_id <= PH_FINAL);
        end else begin
            permit_data = 0;
            arm_notification(0, 1);
            bus_reset = event_id == EV_BUS;
            local_port_reset = event_id == EV_PORT;
            connected = event_id != EV_DISCONNECT;
            // Reset dominates both genuine cancellation sources. Raw SETUP
            // notification is exercised high/low/high throughout held reset.
            if (collision == 1) begin req = 1; setup_token = 1; end
            if (collision == 2) claim_abort = 1;
            setup_received = 1;
            tick();
            req = 0;
            setup_received = 0;
            tick();
            setup_received = 1;
            tick();
            bus_reset = 0; local_port_reset = 0; connected = 1;
            setup_received = 0; setup_token = 0; claim_abort = 0;
            check_reservation_released();
        end
        if (lifecycle_hits[phase_id][event_id] <= before_hits)
            fail($sformatf("Requested lifecycle/event not observed: %s/%s.",
                phase_id.name(), event_id.name()));
        finish_case();
    endtask
    task automatic dma_setup_mask_case();
        reset_case("DMA_SETUP_IMMEDIATE_AND_HELD_MASK", LOCAL_PROFILE_BYTES, 0);
        usbreg_setup = 1;
        #1ps;
        if (dma_setup !== 1'b1) fail("Idle DMA SETUP flag did not pass through.");
        req = 1; setup_token = 1; rx_bytes = 8;
        #1ps;
        if (dma_setup !== 1'b0) fail("Immediate SETUP request did not mask DMA flag.");
        vif.dma_immediate_checks++;
        tick();
        req = 0;
        repeat (4) begin
            tick();
            if (dma_setup !== 1'b0) fail("DMA SETUP mask did not hold awaiting metadata.");
            vif.dma_held_checks++;
        end
        // A matched low/high DMA response retires the held exception.
        dma_valid = 1;
        tick(2);
        if (dma_setup !== 1'b1) fail("DMA SETUP mask did not retire after matched response.");
        dma_valid = 0; usbreg_setup = 0; setup_token = 0;
        finish_case();
    endtask
    task automatic check_mandatory_coverage();
        vif.mandatory_bins = 0;
        for (int p = 0; p < int'(PH_COUNT); p++)
            for (int e = 0; e < int'(EV_COUNT); e++) begin
                if (p == int'(PH_IDLE) && e < int'(EV_BUS)) continue;
                if (lifecycle_hits[p][e] == 0)
                    fail($sformatf("Unhit mandatory lifecycle/event bin %0d/%0d.", p, e));
                vif.mandatory_bins++;
            end
        vif.reset_priority_bins = 0;
        foreach (reset_priority_hits[p,e,c]) begin
            if (reset_priority_hits[p][e][c] == 0)
                fail($sformatf("Unhit reset-priority bin phase/reset/cancel=%0d/%0d/%0d.", p,e,c));
            vif.reset_priority_bins++;
        end
        vif.acceptance_emergency_checks = acceptance_emergency_hits;
        if (acceptance_emergency_hits < 2 || vif.dma_immediate_checks != 1 ||
            vif.dma_held_checks != 4 || vif.reset_setup_high_checks != 72)
            fail("Missing independent acceptance/emergency, DMA mask or reset/raw-SETUP checks.");
    endtask
    task automatic run_cases();
        int unsigned retained_destination;
        full_request(OCP_CMD_INDIRECT_FIFO_DATA, "FIFO_NORMAL_64", LOCAL_PROFILE_DWORDS);
        accept_data(0, 0, 1); wait_words(LOCAL_PROFILE_DWORDS); finish_case();
        label = "FIFO_POST_DRAIN_EMERGENCY";
        retained_destination = destination.size();
        emergency_purge(0);
        if (destination.size() != retained_destination) fail("Published history changed after abort.");
        finish_case();

        full_request(OCP_CMD_INDIRECT_FIFO_DATA, "FIFO_ACCEPTANCE_EDGE_EMERGENCY", 0);
        accept_data(1); emergency_purge(); finish_case();
        full_request(OCP_CMD_INDIRECT_FIFO_DATA, "FIFO_MID_DRAIN_EMERGENCY_5",
            LOCAL_FIFO_PURGE_PREFIX_DWORDS);
        accept_data(); wait_words(LOCAL_FIFO_PURGE_PREFIX_DWORDS);
        emergency_purge(); finish_case();

        reset_case("INCOMPLETE_CAPTURE_EMERGENCY_LATE_SUCCESS", LOCAL_PROFILE_BYTES, 0);
        setup_request(OCP_CMD_INDIRECT_FIFO_DATA, LOCAL_PROFILE_BYTES);
        request_stage(); capture_data(3); emergency_purge();
        // Remaining late RX beats and completion from the purged transaction
        // are not a new request. No fresh endpoint request is supplied.
        capture_data(5);
        end_transfer = 1; success = 1; ready = 1;
        tick(); end_transfer = 0; success = 0; finish_case();

        full_request(OCP_CMD_INDIRECT_FIFO_DATA, "FIFO_EARLY_SETUP_TOKEN", LOCAL_PROFILE_DWORDS);
        accept_data(0, 0, 1); early_setup(); finish_case();
        full_request(OCP_CMD_INDIRECT_FIFO_CTRL, "NONFIFO_FIFO_CTRL_NORMAL_6",
            LOCAL_NONFIFO_DWORDS, LOCAL_NONFIFO_BYTES);
        accept_data(); wait_words(LOCAL_NONFIFO_DWORDS); finish_case();
        full_request(OCP_CMD_INDIRECT_FIFO_CTRL, "NONFIFO_FIFO_CTRL_ACCEPTANCE_EDGE_EMERGENCY",
            0, LOCAL_NONFIFO_BYTES);
        accept_data(1); emergency_purge(); finish_case();
        full_request(OCP_CMD_INDIRECT_FIFO_CTRL, "NONFIFO_FIFO_CTRL_MID_DRAIN_EMERGENCY_1",
            LOCAL_NONFIFO_PURGE_PREFIX_DWORDS, LOCAL_NONFIFO_BYTES);
        accept_data(); wait_words(LOCAL_NONFIFO_PURGE_PREFIX_DWORDS);
        emergency_purge(); finish_case();
        full_request(OCP_CMD_RECOVERY_CTRL, "NONFIFO_SHORT_3_PADDING",
            LOCAL_SHORT_REG_DWORDS, OCP_SPEC_LEN_RECOVERY_CTRL);
        accept_data(); wait_words(LOCAL_SHORT_REG_DWORDS); finish_case();

        reset_case("FIFO_FINAL_RX_BEAT_AND_EOP_SAME_EDGE",
            LOCAL_PROFILE_BYTES, LOCAL_PROFILE_DWORDS);
        setup_request(OCP_CMD_INDIRECT_FIFO_DATA, LOCAL_PROFILE_BYTES);
        request_stage(); capture_data(LOCAL_PROFILE_BYTES / 8, 1);
        wait_words(LOCAL_PROFILE_DWORDS); finish_case();
        full_request(OCP_CMD_INDIRECT_FIFO_DATA, "FIFO_RX_LENGTH_MISMATCH", 0);
        rx_bytes = 12'(LOCAL_PROFILE_BYTES - 4);
        end_transfer = 1; success = 1;
        tick(); end_transfer = 0; success = 0; finish_case();

        full_request(OCP_CMD_INDIRECT_FIFO_DATA, "REJECTED_DATA_NO_ACCEPTANCE", 0);
        accept_data(0, 1); emergency_purge(); finish_case();
        reset_case("IN_COMPLETION_NOT_RX_ACCEPTANCE", LOCAL_PROFILE_BYTES, 0);
        setup_request(OCP_CMD_INDIRECT_FIFO_DATA, LOCAL_PROFILE_BYTES);
        request_stage(); capture_data(LOCAL_PROFILE_BYTES / 8);
        // Event-attribution negative control, not a legal completed IN read:
        // RX bytes were captured but never accepted. A subsequent IN token's
        // completion cannot accept that old RX candidate. No TX response is
        // supplied; this deliberately checks stale synchronized event order.
        tick(); req = 1; dir_in = 1; setup_token = 0;
        tick(); req = 0;
        end_transfer = 1; success = 1; ready = 1;
        tick(); end_transfer = 0; success = 0; finish_case();
        reset_case("ZERO_RX_OUT_PING_LIKE_COMPLETION", LOCAL_PROFILE_BYTES, 0);
        setup_request(OCP_CMD_INDIRECT_FIFO_DATA, LOCAL_PROFILE_BYTES);
        request_stage();
        // No PID port exists here; this only checks a zero-RX completion,
        // not complete wire-level PING classification.
        rx_bytes = 0; end_transfer = 1; success = 1; ready = 1;
        tick(); end_transfer = 0; success = 0; finish_case();
        reset_case("INCOMPLETE_CAPTURE_EXACT_LENGTH_REQUIRED", LOCAL_PROFILE_BYTES, 0);
        setup_request(OCP_CMD_INDIRECT_FIFO_DATA, LOCAL_PROFILE_BYTES);
        request_stage(); capture_data(3);
        end_transfer = 1; success = 1; ready = 1;
        tick(); end_transfer = 0; success = 0; finish_case();

        zero_data_cancel("FIFO_ZERO_DATA_SETUP_CANCEL_PUBLISHED",
            LOCAL_PROFILE_DWORDS, 0);
        zero_data_cancel("FIFO_ZERO_DATA_SETUP_CANCEL_NO_CAPACITY", 0, 0);
        zero_data_cancel("FIFO_ZERO_DATA_EMERGENCY_PUBLISHED",
            LOCAL_PROFILE_DWORDS, 1);
        zero_data_cancel("FIFO_ZERO_DATA_EMERGENCY_NO_CAPACITY", 0, 1);

        reset_case("FIFO_INCOMPLETE_SETUP_CANCEL_3_BEATS", LOCAL_PROFILE_BYTES, 0);
        setup_request(OCP_CMD_INDIRECT_FIFO_DATA, LOCAL_PROFILE_BYTES);
        request_stage(); capture_data(3);
        arm_notification(1, 1);
        setup_token_request();
        check_reservation_released(); finish_case();

        full_request(OCP_CMD_INDIRECT_FIFO_DATA, "FIFO_FINAL_PUSH_EMERGENCY",
            LOCAL_PROFILE_DWORDS - 1);
        accept_data(); wait_words(LOCAL_PROFILE_DWORDS - 1);
        // The would-be final word must not be published on this edge.
        emergency_purge(); finish_case();

        full_request(OCP_CMD_INDIRECT_FIFO_DATA, "FIFO_DONE_CYCLE_EMERGENCY",
            LOCAL_PROFILE_DWORDS);
        accept_data(); wait_words(LOCAL_PROFILE_DWORDS);
        // The last push is already committed; this is its completion tail,
        // not an emergency during the accepted drain.
        emergency_purge(0); finish_case();

        full_request(OCP_CMD_INDIRECT_FIFO_DATA, "FIFO_MIRROR_DRAIN_EMERGENCY",
            LOCAL_FIFO_PURGE_PREFIX_DWORDS + 3);
        accept_data(); wait_words(LOCAL_FIFO_PURGE_PREFIX_DWORDS);
        tick();
        arm_notification(0, 0);
        setup_token_request();
        if (words_seen != LOCAL_FIFO_PURGE_PREFIX_DWORDS + 3)
            fail("Early token changed the exact pre-emergency drain prefix.");
        emergency_purge(); finish_case();

        full_request(OCP_CMD_INDIRECT_FIFO_DATA, "FIFO_COMPLETION_TAIL_SETUP",
            LOCAL_PROFILE_DWORDS);
        accept_data(); wait_words(LOCAL_PROFILE_DWORDS);
        // No intervening tick: the next edge is the decoder completion tail.
        arm_notification(0, 0);
        setup_token_request();
        check_reservation_released();
        finish_replacement_setup(); finish_case();

        full_request(OCP_CMD_INDIRECT_FIFO_DATA, "FIFO_POST_DRAIN_SETUP_NO_STATUS",
            LOCAL_PROFILE_DWORDS);
        accept_data(); wait_words(LOCAL_PROFILE_DWORDS); tick(4);
        check_reservation_released();
        arm_notification(0, 1);
        setup_token_request();
        finish_replacement_setup(); finish_case();

        full_request(OCP_CMD_INDIRECT_FIFO_DATA, "FIFO_NINTH_CURRENT_BEAT_EOP", 0);
        // Eight stored beats plus this current beat is nine, not a saturated
        // eight. Reported bytes alone must not qualify this payload.
        rx_valid = 1; rx_data = 64'hD1D2D3D4D5D6D7D8;
        rx_bytes = 12'(LOCAL_PROFILE_BYTES); end_transfer = 1; success = 1;
        tick(); rx_valid = 0; end_transfer = 0; success = 0; finish_case();

        full_request(OCP_CMD_INDIRECT_FIFO_DATA, "FIFO_PARTIAL_WORD_BYTE_MISMATCH", 0);
        rx_bytes = 12'(LOCAL_PROFILE_BYTES - 1);
        end_transfer = 1; success = 1;
        tick(); end_transfer = 0; success = 0; finish_case();

        full_request(OCP_CMD_INDIRECT_FIFO_DATA, "SETUP_COMPLETION_NOT_RX_ACCEPTANCE", 0);
        // A replacement SETUP completion without its own body cannot accept
        // bytes captured for the old OUT request.
        arm_notification(1, 1);
        setup_token_request();
        end_transfer = 1; success = 1;
        tick(); setup_token = 0; end_transfer = 0; success = 0; finish_case();

        reset_pending_rx("FIFO_BUS_RESET_PENDING_RX_5", 1);
        reset_pending_rx("FIFO_LOCAL_PORT_RESET_PENDING_RX_5", 0);
        for (int p = 0; p < int'(PH_COUNT); p++)
            for (int e = 0; e < int'(EV_COUNT); e++) begin
                if (p == int'(PH_IDLE) && e < int'(EV_BUS)) continue;
                lifecycle_case(lifecycle_t'(p), event_t'(e));
            end
        // Pending and would-be-final publication expose both reset priorities
        // without relying on emergency-masked DUT valid/good signals.
        for (int p = 0; p < 2; p++)
            for (int e = int'(EV_BUS); e <= int'(EV_DISCONNECT); e++)
                for (int c = 1; c <= 2; c++)
                    lifecycle_case(p == 0 ? PH_PENDING : PH_FINAL, event_t'(e), c);
        dma_setup_mask_case();
    endtask

    initial begin
        forever begin
            wait (vif.start === 1'b1 &&
                  vif.request_generation !== vif.completed_generation);
            vif.done = 0; vif.running = 1; vif.errors = 0; vif.cases = 0;
            vif.fifo_bound_checks = 0;
            vif.notification_checks = 0;
            vif.reset_boundary_checks = 0;
            foreach (lifecycle_hits[p,e]) lifecycle_hits[p][e] = 0;
            foreach (reset_priority_hits[p,e,c]) reset_priority_hits[p][e][c] = 0;
            acceptance_emergency_hits = 0;
            vif.reset_setup_high_checks = 0;
            vif.dma_immediate_checks = 0; vif.dma_held_checks = 0;
            run_cases();
            check_mandatory_coverage();
            if (vif.errors != 0 || vif.cases != vif.EXPECTED_CASES ||
                vif.fifo_bound_checks != vif.EXPECTED_FIFO_BOUND_CHECKS || fifo_bound_active ||
                vif.notification_checks != vif.EXPECTED_NOTIFICATION_CHECKS || event_armed ||
                vif.reset_boundary_checks != vif.EXPECTED_RESET_BOUNDARY_CHECKS)
                fail("Missing directed cases or checker errors.");
            `uvm_info("OCP_RX_DRAIN_UNIT",
                $sformatf("RX_DRAIN_COUNTS clock_mhz=%0d cases=%0d fifo_bounds=%0d notifications=%0d reset_boundaries=%0d",
                    CLOCK_MHZ, vif.cases, vif.fifo_bound_checks,
                    vif.notification_checks, vif.reset_boundary_checks), UVM_NONE)
            `uvm_info("OCP_RX_DRAIN_UNIT",
                $sformatf("RX_MANDATORY_COVERAGE clock_mhz=%0d lifecycle=%0d reset_priority=%0d acceptance_emergency=%0d raw_setup_during_reset=%0d dma_immediate/held=%0d/%0d",
                    CLOCK_MHZ, vif.mandatory_bins, vif.reset_priority_bins,
                    vif.acceptance_emergency_checks, vif.reset_setup_high_checks,
                    vif.dma_immediate_checks, vif.dma_held_checks), UVM_NONE)
            tick();
            check_sink = 0; reset_n = 0; vif.running = 0;
            vif.completed_generation = vif.request_generation;
            vif.done = 1;
        end
    end
endmodule
