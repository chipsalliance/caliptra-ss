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
  logic [7:0] attempt_bytes[$];
  logic [7:0] first_bytes[$];
  svt_usb_packet::pid_name_enum first_pid;

  function new(string name = "usb_ocp_ep0_retry_control");
    super.new(name);
  endfunction

  function void ocp_configure_request(svt_usb_transfer transfer, retry_kind_e selected);
    if (original != null || transfer == null ||
        transfer.xfer_type != svt_usb_transfer::CONTROL_TRANSFER ||
        transfer.endpoint_number != 0 || transfer.setup_data_w_length == 0)
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
    first_bytes.delete();
    attempt_bytes.delete();
    `uvm_info("OCP_EP0_RETRY_START", $sformatf(
      "kind=%s native=%0d addr=%0d command=0x%02h wLength=%0d",
      kind.name(),original.get_inst_id(),original.device_address,
      original.setup_data_w_value,original.setup_data_w_length), UVM_NONE)
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
        if (kind == WRITE_RETRY && data_tokens == 2 && !write_committed_before_retry)
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
      if (host_tx != (token_pid == svt_usb_packet::IN))
        `uvm_fatal("OCP_EP0_RETRY_WIRE", "Handshake direction differs from the observed token")
      if (kind == WRITE_RETRY && data_direction && data_packets > 1 &&
          loss_applied && pid != svt_usb_packet::ACK)
        `uvm_fatal("OCP_EP0_RETRY_DUPLICATE", $sformatf(
          "USB 2.0 8.6.4: accepted OUT duplicate requires ACK, received %s",
          pid.name()))
      if (pid inside {svt_usb_packet::ACK,svt_usb_packet::NYET}) begin
        if (data_direction) data_acks++;
        else status_acked = 1;
      end else if (pid == svt_usb_packet::NAK) naks++;
      `uvm_info("OCP_EP0_RETRY_HANDSHAKE", $sformatf(
        "kind=%s token=%s pid=%s host_tx=%0b",kind.name(),token_pid.name(),
        pid.name(),host_tx), UVM_NONE)
      target_token = 0;
    end
  endfunction

  function void ocp_check_completion();
    expected_timeout_armed = 0;
    `uvm_info("OCP_EP0_RETRY_RESULT", $sformatf(
      "kind=%s native=%0d status=%s loss=%0b setups=%0d tokens=%0d data=%0d ACKs=%0d NAKs=%0d status_acked=%0b committed_before_retry=%0b",
      kind.name(),original.get_inst_id(),original.status.name(),loss_applied,
      setup_tokens,data_tokens,data_packets,data_acks,naks,status_acked,
      write_committed_before_retry), UVM_NONE)
    if (!loss_applied || setup_tokens != 1 || data_packets < 2 || data_tokens < 2)
      `uvm_error("OCP_EP0_RETRY_INJECTION", "One-shot loss and same-CONTROL wire retry were not established")
    if (original.status != svt_sequence_item::ACCEPT || !status_acked ||
        data_acks < (kind == READ_RETRY ? 1 : 2))
      `uvm_error("OCP_EP0_RETRY_RECOVERY", "Native CONTROL retry failed to recover through acknowledged Status")
    original = null;
  endfunction
endclass

class usb_ocp_ep0_retry_timeout_catcher extends uvm_report_catcher;
  `uvm_object_utils(usb_ocp_ep0_retry_timeout_catcher)
  usb_ocp_ep0_retry_control control;

  function new(string name = "usb_ocp_ep0_retry_timeout_catcher");
    super.new(name);
  endfunction

  virtual function action_e catch();
    string native_id;
    if (control == null || control.original == null ||
        control.kind != usb_ocp_ep0_retry_control::WRITE_RETRY ||
        !control.expected_timeout_armed || !control.loss_applied ||
        control.expected_timeout_seen || !control.write_committed_before_retry ||
        control.setup_tokens != 1 || control.data_tokens != 1 ||
        control.data_packets != 1 || control.data_acks != 1 ||
        control.first_pid != svt_usb_packet::DATA1)
      return THROW;
    native_id = $sformatf(
      "register_fail:PROTOCOL TRANSACTOR:IN-LINE:device_response_timeout_check_Dev%0d_EP0",
      control.original.device_address);
    if (get_severity() == UVM_ERROR && get_id() == native_id) begin
      control.expected_timeout_seen = 1;
      set_message($sformatf(
        "Expected timeout after one host-side received-handshake drop; %s: %s",
        native_id,get_message()));
      set_id("OCP_EP0_RETRY_EXPECTED_TIMEOUT");
      set_severity(UVM_INFO);
      set_action(UVM_DISPLAY);
    end
    return THROW;
  endfunction
endclass

class usb_ocp_ep0_retry_observer extends usb_ocp_observer;
  `uvm_component_utils(usb_ocp_ep0_retry_observer)
  usb_ocp_ep0_retry_control control;

  function new(string name = "usb_ocp_ep0_retry_observer", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual function void ocp_configure_transfer_snapshot(
      svt_usb_transfer xfer, usb_ocp_event item);
    if (control != null && xfer == control.selected_transfer &&
        control.kind == usb_ocp_ep0_retry_control::WRITE_RETRY &&
        control.loss_applied && control.expected_timeout_seen)
      item.expected_device_timeout = 1;
  endfunction
endclass

class usb_ocp_ep0_retry_callback extends svt_usb_protocol_callback;
  `uvm_object_utils(usb_ocp_ep0_retry_callback)
  usb_ocp_ep0_retry_control control;
  bit out_wait;

  function new(string name = "usb_ocp_ep0_retry_callback");
    super.new(name);
  endfunction

  virtual function void pre_usb_20_packet_out_port_put(
      svt_usb_protocol component, int chan_id, svt_usb_packet packet,
      svt_usb_transaction transaction, int packet_ix,
      svt_usb_transfer transfer, int transaction_ix, ref bit drop);
    if (packet == null || control == null)
      `uvm_fatal("OCP_EP0_RETRY_SCOPE", "Missing native packet or retry control")
    if (packet.pid_type == svt_usb_packet::TOKEN &&
        packet.get_pid_name_val() != svt_usb_packet::SOF) begin
      control.expected_timeout_armed = 0;
      out_wait = 0;
    end
    if (drop || control.original == null ||
        control.kind != usb_ocp_ep0_retry_control::WRITE_RETRY ||
        control.loss_applied || transfer != control.original || transaction == null)
      return;
    if (transaction.get_xact_type_val() == svt_usb_types::OUT_TRANSACTION &&
        packet.pid_type == svt_usb_packet::DATA &&
        packet.get_pid_name_val() == svt_usb_packet::DATA1)
      out_wait = 1;
  endfunction

  // Drop at the host's protocol input, after wire observation but before
  // accepting ACK/NYET. USB 2.0 8.6.4 requires retransmission, not a new SETUP.
  virtual function void post_usb_20_packet_in_port_get(
      svt_usb_protocol component, int chan_id, svt_usb_packet packet, ref bit drop);
    if (!out_wait || control.original == null || control.loss_applied ||
        packet == null || drop || packet.pid_type != svt_usb_packet::HANDSHAKE)
      return;
    out_wait = 0;
    if (packet.get_pid_name_val() inside {svt_usb_packet::ACK,svt_usb_packet::NYET}) begin
      if (!control.skip_loss) begin
        control.expected_timeout_armed = 1;
        drop = 1;
        control.loss_applied = 1;
        `uvm_info("OCP_EP0_RETRY_LOSS", "Host protocol discards one received OUT ACK/NYET", UVM_NONE)
      end
    end
  endfunction

  virtual function void randomized_transaction(svt_usb_protocol component,
      svt_usb_transfer transfer, int transaction_ix,
      svt_usb_types::protocol_randomization_point_enum rand_point);
    svt_usb_transaction transaction;
    svt_usb_transaction::host_response_enum wanted;
    int unsigned old_normal;
    int unsigned old_timeout;
    bit ok;
    if (control.original == null || transfer != control.original ||
        control.kind != usb_ocp_ep0_retry_control::READ_RETRY ||
        rand_point != svt_usb_types::PROTOCOL_GEN_20_TRANSACTION_HOST_RESPONSE)
      return;
    if (transaction_ix < 0 || transaction_ix >= transfer.implementation.size() ||
        !$cast(transaction,transfer.implementation[transaction_ix]) || transaction == null)
      `uvm_fatal("OCP_EP0_RETRY_SCOPE", "Invalid native transaction response index")
    if (transaction.get_xact_type_val() != svt_usb_types::IN_TRANSACTION) return;
    wanted = control.loss_applied || control.skip_loss ?
             svt_usb_transaction::HOST_NORMAL_RESPONSE :
             svt_usb_transaction::HOST_TIMEOUT_RESPONSE;
    old_normal = transaction.NORMAL_RESPONSE_wt;
    old_timeout = transaction.TIMEOUT_RESPONSE_wt;
    transaction.NORMAL_RESPONSE_wt = wanted == svt_usb_transaction::HOST_NORMAL_RESPONSE;
    transaction.TIMEOUT_RESPONSE_wt = wanted == svt_usb_transaction::HOST_TIMEOUT_RESPONSE;
    ok = transaction.randomize(host_response);
    transaction.NORMAL_RESPONSE_wt = old_normal;
    transaction.TIMEOUT_RESPONSE_wt = old_timeout;
    if (!ok || transaction.host_response != wanted)
      `uvm_fatal("OCP_EP0_RETRY_INJECTION", "Native host response randomization failed")
    if (wanted == svt_usb_transaction::HOST_TIMEOUT_RESPONSE) begin
      control.loss_applied = 1;
      `uvm_info("OCP_EP0_RETRY_LOSS", "Host omits one ACK after received IN DATA", UVM_NONE)
    end
  endfunction
endclass

class usb_ocp_ep0_retry_packet_callback extends svt_usb_link_monitor_callback;
  `uvm_object_utils(usb_ocp_ep0_retry_packet_callback)
  usb_ocp_ep0_retry_control control;

  function new(string name = "usb_ocp_ep0_retry_packet_callback");
    super.new(name);
  endfunction

  virtual function void usb_20_tx_packet_ended(svt_usb_link_monitor link_mon,
                                               svt_usb_packet pkt);
    if (control == null) `uvm_fatal("OCP_EP0_RETRY_SCOPE", "Missing retry wire observer")
    control.ocp_capture_packet(pkt,1);
  endfunction

  virtual function void usb_20_rx_packet_ended(svt_usb_link_monitor link_mon,
                                               svt_usb_packet pkt);
    if (control == null) `uvm_fatal("OCP_EP0_RETRY_SCOPE", "Missing retry wire observer")
    control.ocp_capture_packet(pkt,0);
  endfunction
endclass
