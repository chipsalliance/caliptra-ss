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

class usb_ocp_ep0_retry_control extends uvm_object;
  `uvm_object_utils(usb_ocp_ep0_retry_control)
  typedef enum {READ_RETRY, WRITE_RETRY} retry_kind_e;
  svt_usb_transfer original;
  svt_usb_transfer selected_transfer;
  bit expected_timeout_armed;
  bit status_probe;
  retry_kind_e kind;
  svt_usb_packet::pid_name_enum token_pid;
  bit target_token;
  bit setup_data;
  bit loss_applied;
  bit status_acked;
  bit write_committed_before_retry;
  bit skip_loss;
  bit expected_timeout_seen;
  int unsigned data_packets;
  int unsigned data_tokens;
  int unsigned data_acks;
  int unsigned naks;
  int unsigned setup_tokens;
  svt_usb_transaction loss_transaction;
  int loss_transaction_ix = -1;
  int unsigned loss_data_tokens;
  int unsigned loss_data_packets;
  int unsigned loss_data_acks;
  int unsigned data_naks;
  int unsigned status_naks;
  logic [7:0] attempt_bytes[$];
  logic [7:0] first_bytes[$];
  svt_usb_packet::pid_name_enum first_pid;

  function new(string name = "usb_ocp_ep0_retry_control");
    super.new(name);
  endfunction

  function void ocp_configure_request(svt_usb_transfer transfer, retry_kind_e selected);
    if (original != null || transfer == null ||
        transfer.xfer_type != svt_usb_transfer::CONTROL_TRANSFER ||
        transfer.endpoint_number != 0 ||
        (!status_probe && transfer.setup_data_w_length == 0))
      `uvm_fatal("OCP_EP0_RETRY_SCOPE", "Invalid or overlapping native CONTROL retry request")
    original = transfer;
    selected_transfer = transfer;
    kind = selected;
    target_token = 0;
    setup_data = 0;
    loss_applied = 0;
    status_acked = 0;
    write_committed_before_retry = 0;
    expected_timeout_seen = 0;
    expected_timeout_armed = 0;
    data_packets = 0;
    data_tokens = 0;
    data_acks = 0;
    naks = 0;
    setup_tokens = 0;
    loss_transaction = null;
    loss_transaction_ix = -1;
    loss_data_tokens = 0;
    loss_data_packets = 0;
    loss_data_acks = 0;
    data_naks = 0;
    status_naks = 0;
    first_bytes.delete();
    attempt_bytes.delete();
    `uvm_info("OCP_EP0_RETRY_START", $sformatf(
      "kind=%s native=%0d addr=%0d command=0x%02h wLength=%0d",
      kind.name(),original.get_inst_id(),original.device_address,
      original.setup_data_w_value,original.setup_data_w_length), UVM_NONE)
  endfunction

  function void ocp_record_loss(svt_usb_transaction transaction, int transaction_ix);
    if (original == null || loss_applied || transaction == null ||
        transaction_ix < 0 || transaction_ix >= original.implementation.size() ||
        original.implementation[transaction_ix] != transaction ||
        data_tokens == 0 || data_packets == 0 ||
        (kind == WRITE_RETRY && data_acks == 0))
      `uvm_fatal("OCP_EP0_RETRY_INJECTION", "Loss lacks the selected native transaction and wire acceptance")
    loss_transaction = transaction;
    loss_transaction_ix = transaction_ix;
    loss_data_tokens = data_tokens;
    loss_data_packets = data_packets;
    loss_data_acks = data_acks;
    loss_applied = 1;
    `uvm_info("OCP_EP0_RETRY_ANCHOR", $sformatf(
      "kind=%s transaction=%0d token=%0d DATA=%0d accepting_handshakes=%0d preceding_NAKs=%0d",
      kind.name(),transaction_ix,loss_data_tokens,loss_data_packets,loss_data_acks,data_naks),
      UVM_NONE)
  endfunction

  function bit ocp_post_loss_token_seen();
    return loss_applied && data_tokens > loss_data_tokens;
  endfunction

  function void ocp_capture_packet(svt_usb_packet packet, bit host_tx);
    svt_usb_packet::pid_name_enum pid;
    bit data_direction;
    if (original == null) return;
    if (packet == null)
      `uvm_fatal("OCP_EP0_RETRY_WIRE", "Missing monitor packet")
    pid = packet.get_pid_name_val();
    if (host_tx && packet.pid_type == svt_usb_packet::TOKEN) begin
      if (pid == svt_usb_packet::SOF) return;
      target_token = packet.device_address == original.device_address &&
                     packet.ept_num == original.endpoint_number;
      token_pid = pid;
      setup_data = pid == svt_usb_packet::SETUP;
      if (!target_token) return;
      if (setup_data) begin
        setup_tokens++;
        if (setup_tokens != 1)
          `uvm_fatal("OCP_EP0_RETRY_SCOPE", "Retry was replaced by another SETUP")
      end else if (pid == (kind == READ_RETRY ? svt_usb_packet::IN : svt_usb_packet::OUT)) begin
        data_tokens++;
        if (kind == WRITE_RETRY && ocp_post_loss_token_seen() && !write_committed_before_retry)
          `uvm_error("OCP_EP0_RETRY_BOUNDARY", "Repeated OUT preceded public WRITE_INDEX commit evidence")
      end
      return;
    end
    if (!target_token || setup_data ||
        !(token_pid inside {svt_usb_packet::IN,svt_usb_packet::OUT})) return;
    data_direction = token_pid == (kind == READ_RETRY ?
                                  svt_usb_packet::IN : svt_usb_packet::OUT);
    if (packet.pid_type == svt_usb_packet::DATA) begin
      if (host_tx != (token_pid == svt_usb_packet::OUT) || packet.crc_error_detected())
        `uvm_fatal("OCP_EP0_RETRY_WIRE", "Wrong packet direction or corrupted retry data")
      attempt_bytes.delete();
      for (int i = 0; i < packet.get_payload_byte_count(); i++)
        attempt_bytes.push_back(packet.payload.get_byte_val(packet.payload_offset+i));
      if (data_direction) begin
        data_packets++;
        if (data_packets == 1) begin
          first_bytes = attempt_bytes;
          first_pid = pid;
        end else begin
          // USB 2.0 8.6.4: retransmission preserves PID, length and bytes.
          // Check identity independently of native protocol-checker support.
          if (pid != first_pid || attempt_bytes.size() != first_bytes.size())
            `uvm_error("OCP_EP0_RETRY_IDENTITY", "Retried packet changed PID or length")
          else begin
            foreach (first_bytes[i])
              if (attempt_bytes[i] !== first_bytes[i]) begin
                `uvm_error("OCP_EP0_RETRY_IDENTITY", $sformatf(
                  "kind=%s retry=%0d byte=%0d first=0x%02h repeated=0x%02h",
                  kind.name(),data_packets,i,first_bytes[i],attempt_bytes[i]))
                break;
              end
          end
        end
        `uvm_info("OCP_EP0_RETRY_WIRE", $sformatf(
          "kind=%s attempt=%0d pid=%s bytes=%p loss_applied=%0b",
          kind.name(),data_packets,pid.name(),attempt_bytes,loss_applied), UVM_NONE)
      end else
        `uvm_info("OCP_EP0_RETRY_STATUS", $sformatf(
          "kind=%s pid=%s bytes=%0d",kind.name(),pid.name(),attempt_bytes.size()), UVM_NONE)
    end else if (packet.pid_type == svt_usb_packet::HANDSHAKE) begin
      // USB 2.0 8.4.5: IN ACK is host-originated; IN NAK/STALL is not.
      if ((token_pid == svt_usb_packet::IN &&
           !(pid inside {svt_usb_packet::ACK,svt_usb_packet::NAK,svt_usb_packet::STALL})) ||
          (token_pid == svt_usb_packet::OUT &&
           !(pid inside {svt_usb_packet::ACK,svt_usb_packet::NYET,
                        svt_usb_packet::NAK,svt_usb_packet::STALL})) ||
          host_tx != (token_pid == svt_usb_packet::IN && pid == svt_usb_packet::ACK))
        `uvm_fatal("OCP_EP0_RETRY_WIRE", "Handshake direction differs from the observed token")
      if (kind == READ_RETRY && data_direction && loss_applied &&
          data_tokens == loss_data_tokens && pid == svt_usb_packet::ACK)
        `uvm_fatal("OCP_EP0_RETRY_INJECTION", "Host ACKed the selected lost-ACK attempt")
      if (kind == WRITE_RETRY && data_direction && ocp_post_loss_token_seen() &&
          !(pid inside {svt_usb_packet::ACK,svt_usb_packet::NYET}))
        `uvm_fatal("OCP_EP0_RETRY_DUPLICATE", $sformatf(
          "Accepted OUT duplicate requires ACK/NYET, received %s",
          pid.name()))
      if (pid == svt_usb_packet::STALL)
        `uvm_fatal("OCP_EP0_RETRY_RECOVERY", "Required-success CONTROL received STALL")
      if (pid inside {svt_usb_packet::ACK,svt_usb_packet::NYET}) begin
        if (data_direction) data_acks++;
        else status_acked = 1;
      end else if (pid == svt_usb_packet::NAK) begin
        naks++;
        if (data_direction) data_naks++;
        else status_naks++;
      end
      `uvm_info("OCP_EP0_RETRY_HANDSHAKE", $sformatf(
        "kind=%s token=%s pid=%s host_tx=%0b",kind.name(),token_pid.name(),
        pid.name(),host_tx), UVM_NONE)
      target_token = 0;
    end
  endfunction

  function void ocp_check_completion();
    expected_timeout_armed = 0;
    `uvm_info("OCP_EP0_RETRY_RESULT", $sformatf(
      "kind=%s native=%0d status=%s loss=%0b setups=%0d tokens=%0d data=%0d ACK_or_NYETs=%0d NAKs=%0d status_acked=%0b committed_before_retry=%0b",
      kind.name(),original.get_inst_id(),original.status.name(),loss_applied,
      setup_tokens,data_tokens,data_packets,data_acks,naks,status_acked,
      write_committed_before_retry), UVM_NONE)
    if (!loss_applied || setup_tokens != 1 || !ocp_post_loss_token_seen() ||
        data_packets <= loss_data_packets)
      `uvm_error("OCP_EP0_RETRY_INJECTION", "One-shot loss and same-CONTROL wire retry were not established")
    if (kind == WRITE_RETRY && loss_applied && !expected_timeout_seen)
      `uvm_error("OCP_EP0_RETRY_INJECTION", "Selected received-handshake loss lacked its expected timeout")
    if (original.status != svt_sequence_item::ACCEPT || !status_acked ||
        data_acks < (kind == READ_RETRY ? 1 : 2))
      `uvm_error("OCP_EP0_RETRY_RECOVERY", "Native CONTROL retry failed to recover through acknowledged Status")
    original = null;
  endfunction

  function void ocp_check_status_probe();
    if (!status_probe || original == null || original.setup_data_w_length != 0 ||
        original.status != svt_sequence_item::ACCEPT || setup_tokens != 1 ||
        status_naks == 0 || !status_acked || loss_applied)
      `uvm_fatal("OCP_EP0_RETRY_NAK", "Native zero-DATA control lacks IN Status NAK and successful completion")
    `uvm_info("OCP_EP0_RETRY_NAK",
      "Native zero-DATA control completed after device IN Status NAK; no retry-loss credit",
      UVM_NONE)
    original = null;
  endfunction
endclass
