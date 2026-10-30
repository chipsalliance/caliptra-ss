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

// Sets EPSKIP during an observed OUT data packet and verifies delayed service.
//
// Relies on the Synopsys SVT USB VIP's built-in protocol packet notification
// (host_agent.prot.NOTIFY_20_HOST_TX_PACKET in
// others/class_svt_usb_protocol.html) to time the EPSKIP register write
// while the 512-byte DATA0 packet (~8.5 us on UTMI) is in flight on the bus,
// and on the VIP's built-in protocol/link checks (enabled by default via
// register_default_chks = 1, enable_default_chks = 1 in protocolChecks.html,
// coverage/class_svt_usb_protocol_ep_sc.html, and
// coverage/class_svt_usb_link_20_sc.html):
//   - svt_usb_protocol_ep_sc:
//     * packet_error_check, data_toggle_check, valid_device_response_check
//   - svt_usb_link_20_sc:
//     * unexpected_response_check
//
// Why a custom cycle-level skip monitor is unnecessary:
//   If hardware retired EPSKIP early while the 512-byte DATA0 packet was still
//   in flight, USB_DMA_1 (READ_EPINFO_SKIP -> WAIT_ON_GNT_FOR_SKIP_UPDATE)
//   would clear Active without modifying NBytes or buffer_offset, and USB_PIE_1
//   would not accept/commit the 512-byte payload. Consequently, the SVT VIP's
//   BULK_OUT_TRANSFER completion (checked for ACCEPT under
//   svt_usb_protocol_ep_sc::valid_device_response_check) combined with
//   verify_inflight_packet() (checking active == 0, nbytes == 512,
//   buffer_offset advanced by 512, and all 512 SRAM bytes) architecturally
//   proves that hardware completed the in-flight packet before retiring EPSKIP.
class usb_dev_skip_during_rx_seq extends usb_dev_skip_seq;
  `uvm_object_utils(usb_dev_skip_during_rx_seq)

  logic [31:0] inflight_buffer_offset = 32'h0000_0200;
  int unsigned inflight_armed_bytes = 1024;
  int unsigned inflight_payload_bytes = 512;
  logic [7:0] inflight_payload_base = 8'h40;
  logic [31:0] inflight_sentinel = 32'hcaca_caca;

  // Token-overlap skip configuration for stimulus intended to intersect
  // arriving token EOP (epinfo_req) with USB_DMA EPSKIP processing.
  localparam logic [31:0] TOKEN_OVERLAP_SKIP_MASK =
    ((32'h1 << (USB_DEV0_NBPHYSEP + 2)) - 1) & ~32'h0000_000f;
  localparam logic [31:0] TOKEN_OVERLAP_EPINUSE_MASK =
    32'h2aaa_aaa0 & TOKEN_OVERLAP_SKIP_MASK;

  logic [31:0] token_overlap_in_buffer_offset = 32'h0000_0900;
  int unsigned token_overlap_in_bytes = 16;
  logic [7:0] token_overlap_in_payload_base = 8'h70;
  int unsigned token_overlap_target_tokens = 5;

  function new(string name = "usb_dev_skip_during_rx_seq");
    super.new(name);
    skip_buffer_offset = 32'h0000_0800;
  endfunction

  // Return the post-transfer buffer byte offset matching the hardware
  // implementation behavior where USB_DMA rounds a non-zero partial 64-byte
  // block up to the next 64-byte boundary on descriptor writeback.
  function logic [31:0] expected_post_transfer_buffer_offset(
    logic [31:0] start_buffer_offset,
    int unsigned transferred_bytes
  );
    return start_buffer_offset + (((transferred_bytes + 63) / 64) * 64);
  endfunction

  // Verify the post-skip recovery payload and check that Active cleared and
  // the descriptor buffer pointer advanced as expected.
  virtual task verify_recovery_transfer();
    usb_ep_entry_t observed_entry;
    logic [31:0] expected_buffer_offset;

    super.verify_recovery_transfer();
    read_endpoint_entry(skip_endpoint, observed_entry);
    expected_buffer_offset = expected_post_transfer_buffer_offset(skip_buffer_offset, recovery_bytes);
    if (observed_entry.active !== 1'b0 ||
        entry_buffer_byte_offset(observed_entry) !== expected_buffer_offset) begin
      `uvm_fatal(
        "USB_SKIP_RX_SEQ",
        $sformatf(
          "Post-skip recovery descriptor writeback invalid on %s: observed %s, expected active=0 nbytes=0 buffer=0x%03h",
          skip_endpoint.convert2string(),
          describe_entry(observed_entry),
          expected_buffer_offset
        )
      )
    end
  endtask

  // Compare the packet committed before the delayed skip writeback.
  task verify_inflight_packet();
    usb_ep_entry_t observed_entry;
    logic [31:0] observed_word;
    logic [31:0] expected_word;

    read_endpoint_entry(skip_endpoint, observed_entry);
    if (observed_entry.active !== 1'b0 ||
        observed_entry.nbytes !== inflight_armed_bytes - inflight_payload_bytes ||
        entry_buffer_byte_offset(observed_entry) !== inflight_buffer_offset + inflight_payload_bytes) begin
      `uvm_fatal(
        "USB_SKIP_RX_SEQ",
        $sformatf(
          "Delayed skip writeback is invalid: observed %s, expected active=0 nbytes=%0d buffer=0x%03h",
          describe_entry(observed_entry),
          inflight_armed_bytes - inflight_payload_bytes,
          inflight_buffer_offset + inflight_payload_bytes
        )
      )
    end

    for (int unsigned offset = 0; offset < inflight_payload_bytes; offset += 4) begin
      expected_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        expected_word[8*lane +: 8] = inflight_payload_base + offset + lane;
      end
      read32(USB_DEV0_SRAM, inflight_buffer_offset + offset, observed_word);
      if (observed_word !== expected_word) begin
        `uvm_fatal(
          "USB_SKIP_RX_SEQ",
          $sformatf(
            "In-flight payload mismatch at offset 0x%03h: data=0x%08h expected=0x%08h",
            offset,
            observed_word,
            expected_word
          )
        )
      end
    end
    `uvm_info("USB_SKIP_RX_SEQ", $sformatf("Delayed skip preserved and committed all %0d in-flight bytes", inflight_payload_bytes), UVM_LOW)
  endtask

  // Wait on the SVT protocol component until the target OUT token completes and
  // the 512-byte DATA0 packet is actively transmitting on UTMI.
  task wait_for_target_out_data_start(svt_usb_agent host_agent);
    bit out_token_seen;
    time stage_timeout;

    out_token_seen = 1'b0;
    stage_timeout = p_sequencer.cfg.transfer_timeout;
    fork
      begin
        fork
          begin
            while (!out_token_seen) begin
              uvm_object tx_obj;
              svt_usb_packet tx_pkt;

              host_agent.prot.NOTIFY_20_HOST_TX_PACKET.wait_trigger_data(tx_obj);
              if ($cast(tx_pkt, tx_obj) &&
                  tx_pkt.get_pid_name_val() == svt_usb_packet::OUT &&
                  tx_pkt.get_device_address_val() == p_sequencer.cfg.device_address &&
                  tx_pkt.get_ept_num_val() == 4'(skip_endpoint.ep_number)) begin
                out_token_seen = 1'b1;
              end
            end
          end
          begin
            #(stage_timeout);
          end
        join_any
        disable fork;
      end
    join
    if (!out_token_seen) begin
      `uvm_fatal(
        "USB_SKIP_RX_SEQ",
        $sformatf(
          "Timed out after %0t waiting for target OUT token on %s",
          stage_timeout,
          skip_endpoint.convert2string()
        )
      )
    end
    // Advance 1 us into the ~8.5 us 512-byte DATA0 packet transmission so
    // UTMI RXACTIVE is high at the DUT when EPSKIP is written.
    #1us;
  endtask

  // Wait on the SVT protocol component until the in-flight DATA packet finishes.
  task wait_for_target_out_data_end(svt_usb_agent host_agent, output realtime data_ended_at);
    bit data_ended;
    time stage_timeout;

    data_ended = 1'b0;
    data_ended_at = 0;
    stage_timeout = p_sequencer.cfg.transfer_timeout;
    fork
      begin
        fork
          begin
            while (!data_ended) begin
              uvm_object tx_obj;
              svt_usb_packet tx_pkt;

              host_agent.prot.NOTIFY_20_HOST_TX_PACKET.wait_trigger_data(tx_obj);
              if ($cast(tx_pkt, tx_obj) &&
                  tx_pkt.get_pid_name_val() inside {svt_usb_packet::DATA0, svt_usb_packet::DATA1}) begin
                data_ended_at = $realtime;
                data_ended = 1'b1;
              end
            end
          end
          begin
            #(stage_timeout);
          end
        join_any
        disable fork;
      end
    join
    if (!data_ended) begin
      `uvm_fatal(
        "USB_SKIP_RX_SEQ",
        $sformatf(
          "Timed out after %0t waiting for in-flight DATA packet completion on %s",
          stage_timeout,
          skip_endpoint.convert2string()
        )
      )
    end
  endtask

  // Enumerate, overlap EPSKIP with an OUT DATA packet, then prove endpoint recovery.
  virtual task body();
    usb_init_seq init_sequence;
    usb_bulk_out_host_seq inflight_host_sequence;
    usb_dev_skip_host_seq recovery_host_sequence;
    usb_ep_entry_t initial_entry;
    svt_usb_agent host_agent;
    realtime skip_write_accepted_at;
    realtime rx_packet_completed_at;
    realtime skip_cleared_at;

    completed = 1'b0;
    `uvm_info("USB_SKIP_RX_SEQ", "Starting endpoint skip-during-receive scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_SKIP_RX_SEQ", "Enumeration did not complete")
    end
    if (!$cast(host_agent, p_sequencer.host_sequencer.get_parent()) ||
        host_agent.prot == null) begin
      `uvm_fatal("USB_SKIP_RX_SEQ", "Unable to resolve the SVT host agent protocol component")
    end

    skip_endpoint = get_endpoint(skip_target_ep_number, skip_target_direction);
    check_buffer_clear_of_endpoint_list("In-flight transfer", inflight_buffer_offset, inflight_armed_bytes);
    check_buffer_clear_of_endpoint_list("Recovery transfer", skip_buffer_offset, recovery_bytes);
    enable_endpoint_interrupt(skip_endpoint);
    clear_endpoint_interrupt(skip_endpoint);
    fill_endpoint_buffer(inflight_buffer_offset, inflight_armed_bytes, inflight_sentinel);
    arm_endpoint(skip_endpoint, inflight_armed_bytes, inflight_buffer_offset, initial_entry);

    inflight_host_sequence = usb_bulk_out_host_seq::type_id::create("inflight_host_sequence");
    inflight_host_sequence.target_endpoint = skip_endpoint;
    inflight_host_sequence.payload_byte_count = inflight_payload_bytes;
    inflight_host_sequence.payload_base = inflight_payload_base;
    inflight_host_sequence.device_address = p_sequencer.cfg.device_address;
    inflight_host_sequence.transfer_label = "In-flight bulk OUT";

    `uvm_info("USB_SKIP_RX_SEQ", "Armed SVT link monitor OUT/DATA observation; starting the bulk transfer", UVM_LOW)
    fork
      begin
        inflight_host_sequence.start(p_sequencer.host_sequencer);
        if (!inflight_host_sequence.completed) begin
          `uvm_fatal("USB_SKIP_RX_SEQ", "In-flight host sequence returned incomplete")
        end
      end
      begin
        wait_for_target_out_data_start(host_agent);
        `uvm_info("USB_SKIP_RX_SEQ", "Observed the target OUT token and DATA packet start; writing EPSKIP while payload reception is active", UVM_LOW)
        fork
          begin
            request_endpoint_skip(skip_endpoint);
            skip_write_accepted_at = $realtime;
            wait_for_endpoint_skip_clear(
                skip_endpoint,
                skip_clear_timeout,
                skip_clear_poll_interval);
            skip_cleared_at = $realtime;
          end
          begin
            wait_for_target_out_data_end(host_agent, rx_packet_completed_at);
          end
        join
        if (skip_write_accepted_at >= rx_packet_completed_at) begin
          `uvm_fatal(
            "USB_SKIP_RX_SEQ",
            $sformatf(
              "EPSKIP write was not accepted during reception: write=%0t receive-end=%0t",
              skip_write_accepted_at,
              rx_packet_completed_at
            )
          )
        end
        `uvm_info(
          "USB_SKIP_RX_SEQ",
          $sformatf("VIP receive ordering: EPSKIP accepted=%0t packet-end=%0t skip-clear=%0t",
                    skip_write_accepted_at, rx_packet_completed_at, skip_cleared_at),
          UVM_LOW
        )
        if (skip_cleared_at < rx_packet_completed_at) begin
          `uvm_fatal(
            "USB_SKIP_RX_SEQ",
            $sformatf(
              "EPSKIP retired before reception completed: clear=%0t receive-end=%0t",
              skip_cleared_at,
              rx_packet_completed_at
            )
          )
        end
      end
    join

    wait_for_endpoint_interrupt(skip_endpoint, recovery_timeout, recovery_poll_interval);
    verify_inflight_packet();

    arm_recovery_transfer();
    recovery_host_sequence = usb_dev_skip_host_seq::type_id::create("recovery_host_sequence");
    recovery_host_sequence.target_endpoint = skip_endpoint;
    recovery_host_sequence.payload_byte_count = recovery_bytes;
    recovery_host_sequence.payload_base = recovery_payload_base;
    recovery_host_sequence.device_address = p_sequencer.cfg.device_address;
    fork
      begin
        recovery_host_sequence.start(p_sequencer.host_sequencer);
        if (!recovery_host_sequence.completed) begin
          `uvm_fatal("USB_SKIP_RX_SEQ", "Recovery host sequence returned incomplete")
        end
      end
      begin
        wait_for_endpoint_interrupt(skip_endpoint, recovery_timeout, recovery_poll_interval);
      end
    join
    verify_recovery_transfer();
    run_token_overlap_skip_check(host_agent);

    completed = 1'b1;
    `uvm_info("USB_SKIP_RX_SEQ", "Endpoint skip-during-receive scenario completed with delayed service and recovery verified", UVM_LOW)
  endtask

  // Drive multi-endpoint EPSKIP updates concurrently with 5 observed IN tokens
  // as stimulus intended to intersect token EOP (epinfo_req) with EPSKIP
  // processing in READ_EPINFO_SKIP and WAIT_ON_GNT_FOR_SKIP_UPDATE, then arm
  // EP1 IN and verify completion.
  task run_token_overlap_skip_check(svt_usb_agent host_agent);
    usb_endpoint_cfg in_endpoint;
    usb_endpoint_cfg dummy_ep2_out;
    usb_endpoint_cfg dummy_ep2_in;
    usb_bulk_in_host_seq in_host_sequence;
    usb_ep_entry_t inactive_in_entry;
    usb_ep_entry_t armed_in_entry;
    usb_ep_entry_t observed_in_entry;
    usb_ep_entry_t dummy_armed_entry;
    usb_ep_entry_t observed_dummy_out_entry;
    usb_ep_entry_t observed_dummy_in_entry;
    logic [31:0] dummy_active_int_mask;
    logic [31:0] data_word;
    logic [31:0] skip_status;
    logic [31:0] interrupt_status;
    logic [31:0] expected_in_buffer_offset;
    int unsigned observed_in_tokens;
    int unsigned skip_wave_writes;
    bit stop_skip_wave;

    in_endpoint = get_endpoint(skip_target_ep_number, USB_DIRECTION_IN);
    dummy_ep2_out = usb_endpoint_cfg::create_endpoint(
      "dummy_ep2_out",
      2,
      USB_DIRECTION_OUT,
      USB_TRANSFER_TYPE_BULK,
      `SVT_USB_HS_BULK_MAX_PACKET_SIZE
    );
    dummy_ep2_in = usb_endpoint_cfg::create_endpoint(
      "dummy_ep2_in",
      2,
      USB_DIRECTION_IN,
      USB_TRANSFER_TYPE_BULK,
      `SVT_USB_HS_BULK_MAX_PACKET_SIZE
    );
    dummy_active_int_mask = dummy_ep2_out.csr_bit_mask() | dummy_ep2_in.csr_bit_mask();
    check_buffer_clear_of_endpoint_list(
      "Token-overlap bulk IN",
      token_overlap_in_buffer_offset,
      token_overlap_in_bytes
    );

    for (int unsigned offset = 0; offset < token_overlap_in_bytes; offset += 4) begin
      data_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        data_word[8*lane +: 8] = token_overlap_in_payload_base + offset + lane;
      end
      write32(USB_DEV0_SRAM, token_overlap_in_buffer_offset + offset, data_word);
    end

    inactive_in_entry = endpoint_entry(1'b0, 1'b0, token_overlap_in_bytes, token_overlap_in_buffer_offset);
    write_endpoint_entry(in_endpoint, inactive_in_entry);
    enable_endpoint_interrupt(in_endpoint);
    clear_endpoint_interrupt(in_endpoint);

    // Arm dummy EP2 OUT (physical 4, buffer 0) and EP2 IN (physical 5, buffer 1
    // with EPINUSE set) so READ_EPINFO_SKIP exercises both 64-bit word halves.
    dummy_armed_entry = endpoint_entry(1'b1, 1'b0, 0, 0);
    write_endpoint_entry(dummy_ep2_out, dummy_armed_entry, 0);
    write_endpoint_entry(dummy_ep2_in, dummy_armed_entry, 1);
    ral_write32("EPBUFCFG", p_sequencer.reg_model.combo.dev0_csr.EPBUFCFG, TOKEN_OVERLAP_SKIP_MASK);
    ral_write32("EPINUSE", p_sequencer.reg_model.combo.dev0_csr.EPINUSE, TOKEN_OVERLAP_EPINUSE_MASK);
    ral_write32("INTSTAT", p_sequencer.reg_model.combo.dev0_csr.INTSTAT, TOKEN_OVERLAP_SKIP_MASK);

    in_host_sequence = usb_bulk_in_host_seq::type_id::create("token_overlap_in_host_sequence");
    in_host_sequence.target_endpoint = in_endpoint;
    in_host_sequence.payload_byte_count = token_overlap_in_bytes;
    in_host_sequence.payload_base = token_overlap_in_payload_base;
    in_host_sequence.device_address = p_sequencer.cfg.device_address;
    in_host_sequence.bulk_transfer_timeout = recovery_timeout;
    in_host_sequence.transfer_label = "Token-overlap bulk IN";

    observed_in_tokens = 0;
    skip_wave_writes = 0;
    stop_skip_wave = 1'b0;
    `uvm_info(
      "USB_SKIP_RX_SEQ",
      $sformatf(
        "Starting token-overlap EPSKIP phase across %0d IN tokens on %s (EPSKIP mask=0x%08h)",
        token_overlap_target_tokens,
        in_endpoint.convert2string(),
        TOKEN_OVERLAP_SKIP_MASK
      ),
      UVM_LOW
    )

    fork
      begin
        in_host_sequence.start(p_sequencer.host_sequencer);
        if (!in_host_sequence.completed) begin
          `uvm_fatal("USB_SKIP_RX_SEQ", "Token-overlap bulk IN host sequence returned incomplete")
        end
      end
      begin
        fork
          begin
            fork
              begin
                while (observed_in_tokens < token_overlap_target_tokens) begin
                  uvm_object tx_obj;
                  svt_usb_packet tx_pkt;

                  host_agent.prot.NOTIFY_20_HOST_TX_PACKET.wait_trigger_data(tx_obj);
                  if ($cast(tx_pkt, tx_obj) &&
                      tx_pkt.get_pid_name_val() == svt_usb_packet::IN &&
                      tx_pkt.get_device_address_val() == p_sequencer.cfg.device_address &&
                      tx_pkt.get_ept_num_val() == 4'(in_endpoint.ep_number)) begin
                    observed_in_tokens++;
                  end
                end
                stop_skip_wave = 1'b1;
              end
              begin
                #(recovery_timeout);
                if (observed_in_tokens < token_overlap_target_tokens) begin
                  `uvm_fatal(
                    "USB_SKIP_RX_SEQ",
                    $sformatf(
                      "Timed out after %0t waiting for %0d IN tokens during EPSKIP overlap (observed %0d)",
                      recovery_timeout,
                      token_overlap_target_tokens,
                      observed_in_tokens
                    )
                  )
                end
              end
            join_any
            disable fork;
          end
          begin
            while (!stop_skip_wave) begin
              ral_write32("EPSKIP", p_sequencer.reg_model.combo.dev0_csr.EPSKIP, TOKEN_OVERLAP_SKIP_MASK);
              skip_wave_writes++;
              #((skip_wave_writes % 11) * 3ns + 15ns);
            end
          end
        join

        poll_csr_bits(
          "Token-overlap EPSKIP self-clear",
          p_sequencer.reg_model.combo.dev0_csr.EPSKIP,
          TOKEN_OVERLAP_SKIP_MASK,
          1'b0,
          skip_clear_timeout,
          skip_status,
          skip_clear_poll_interval
        );
        read_endpoint_entry(dummy_ep2_out, observed_dummy_out_entry, 0);
        read_endpoint_entry(dummy_ep2_in, observed_dummy_in_entry, 1);
        if (observed_dummy_out_entry.active !== 1'b0 ||
            observed_dummy_in_entry.active !== 1'b0) begin
          `uvm_fatal(
            "USB_SKIP_RX_SEQ",
            $sformatf(
              "Token-overlap skip did not clear dummy entries: ep2_out=%s ep2_in=%s",
              describe_entry(observed_dummy_out_entry),
              describe_entry(observed_dummy_in_entry)
            )
          )
        end
        ral_read32("INTSTAT", p_sequencer.reg_model.combo.dev0_csr.INTSTAT, interrupt_status);
        if ((interrupt_status & dummy_active_int_mask) !== dummy_active_int_mask) begin
          `uvm_fatal(
            "USB_SKIP_RX_SEQ",
            $sformatf(
              "Token-overlap skip did not assert dummy endpoint INTSTAT bits 0x%08h; INTSTAT=0x%08h",
              dummy_active_int_mask,
              interrupt_status
            )
          )
        end
        ral_write32("EPINUSE", p_sequencer.reg_model.combo.dev0_csr.EPINUSE, 32'h0);
        ral_write32("EPBUFCFG", p_sequencer.reg_model.combo.dev0_csr.EPBUFCFG, 32'h0);
        ral_write32("INTSTAT", p_sequencer.reg_model.combo.dev0_csr.INTSTAT, TOKEN_OVERLAP_SKIP_MASK);

        `uvm_info(
          "USB_SKIP_RX_SEQ",
          $sformatf(
            "Observed %0d IN tokens across %0d EPSKIP writes; arming %s to complete transfer",
            observed_in_tokens,
            skip_wave_writes,
            in_endpoint.convert2string()
          ),
          UVM_LOW
        )
        clear_endpoint_interrupt(in_endpoint);
        arm_endpoint(in_endpoint, token_overlap_in_bytes, token_overlap_in_buffer_offset, armed_in_entry);
        wait_for_endpoint_interrupt(in_endpoint, recovery_timeout, recovery_poll_interval);
      end
    join

    read_endpoint_entry(in_endpoint, observed_in_entry);
    expected_in_buffer_offset = expected_post_transfer_buffer_offset(
      token_overlap_in_buffer_offset,
      token_overlap_in_bytes
    );
    if (observed_in_entry.active !== 1'b0 ||
        observed_in_entry.nbytes !== 0 ||
        entry_buffer_byte_offset(observed_in_entry) !== expected_in_buffer_offset) begin
      `uvm_fatal(
        "USB_SKIP_RX_SEQ",
        $sformatf(
          "Token-overlap bulk IN descriptor writeback invalid on %s: observed %s, expected active=0 nbytes=0 buffer=0x%03h",
          in_endpoint.convert2string(),
          describe_entry(observed_in_entry),
          expected_in_buffer_offset
        )
      )
    end
    `uvm_info(
      "USB_SKIP_RX_SEQ",
      $sformatf(
        "Token-overlap EPSKIP phase verified: in_tokens=%0d skip_writes=%0d bytes=%0d",
        observed_in_tokens,
        skip_wave_writes,
        token_overlap_in_bytes
      ),
      UVM_LOW
    )
  endtask
endclass
