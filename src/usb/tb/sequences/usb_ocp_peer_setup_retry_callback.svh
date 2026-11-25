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

class usb_ocp_peer_setup_retry_callback extends svt_usb_protocol_20_host_rx_pid_check_error;
  `uvm_object_utils(usb_ocp_peer_setup_retry_callback)
  localparam time SETUP_RETRY_GAP = 32us;
  // USB 2.0 8.3.1/Table 8-1: ACK PID 0010 has complement 1101.
  localparam bit [3:0] ACK_PID_CHECK = 4'b1101;
  bit configured;
  bit checked;
  bit pending_setup;
  bit immediate_retry;
  logic [6:0] address;
  int unsigned setup_tokens;
  int unsigned rejected_acks;
  svt_usb_transfer native_transfer;
  uvm_report_object expected_reporter;
  svt_usb_packet injected_packet;
  bit expected_error_armed;
  bit injection_confirmed;
  int selected_transaction_ix = -1;
  int unsigned expected_errors;
  string extra_pid_mode;
  int unsigned extra_pid_injections;

  function new(string name = "usb_ocp_peer_setup_retry_callback");
    super.new(name);
  endfunction

  function void ocp_configure_retry(logic [6:0] target_address);
    if (configured || $isunknown(target_address) || target_address == 0)
      `uvm_fatal("OCP_SETUP_RETRY", "Retry requires one configured peer control")
    address = target_address;
    immediate_retry = $test$plusargs("usb_ocp_peer_setup_retry=immediate");
    configured = 1;
    `uvm_info("OCP_SETUP_RETRY",$sformatf(
      "Configured peer SETUP replay address=%0d immediate_retry=%0b",
      address,immediate_retry),UVM_NONE)
  endfunction

  virtual function void pre_usb_20_packet_out_port_put(
      svt_usb_protocol component, int chan_id, svt_usb_packet packet,
      svt_usb_transaction transaction, int packet_ix,
      svt_usb_transfer transfer, int transaction_ix, ref bit drop);
    if (!configured || checked) return;
    if (packet == null) `uvm_fatal("OCP_SETUP_RETRY", "Null host transmit packet")
    if (packet.pid_name inside {svt_usb_packet::SETUP,svt_usb_packet::IN,
                               svt_usb_packet::OUT,svt_usb_packet::PING}) begin
      expected_error_armed = 0;
      pending_setup = packet.pid_name == svt_usb_packet::SETUP &&
        packet.device_address === address && packet.ept_num === 0;
      if (pending_setup) begin
        if (transfer == null || transaction == null ||
            transfer.xfer_type != svt_usb_transfer::CONTROL_TRANSFER ||
            transfer.device_address !== address || transfer.endpoint_number != 0 ||
            transfer.setup_data_bmrequesttype_dir != svt_usb_types::DEVICE_TO_HOST ||
            transfer.setup_data_bmrequesttype_type != svt_usb_types::STANDARD ||
            transfer.setup_data_bmrequesttype_recipient != svt_usb_types::BMREQ_DEVICE ||
            transfer.setup_data_brequest != svt_usb_types::GET_CONFIGURATION ||
            transfer.setup_data_w_value != 0 || transfer.setup_data_w_index != 0 ||
            transfer.setup_data_w_length != 1)
          `uvm_fatal("OCP_SETUP_RETRY", "Peer SETUP lacks the selected native GET_CONFIGURATION context")
        if (native_transfer == null) native_transfer = transfer;
        else if (native_transfer != transfer)
          `uvm_fatal("OCP_SETUP_RETRY", "Peer SETUP retry changed native transfer identity")
        setup_tokens++;
        selected_transaction_ix = transaction_ix;
        if (setup_tokens > (extra_pid_mode == "repeat" ? 3 : 2))
          `uvm_fatal("OCP_SETUP_RETRY", "Unexpected additional peer SETUP retry")
        if (setup_tokens >= 2 && !immediate_retry) begin
          // Directed host backoff lets software service the original SETUP.
          // This tests correlation, not the minimum retry-latency boundary.
          // The longint helper is valid only during randomization.
          packet.inter_pkt_usb_20_diff_source_delay =
            usb_vip_cfg_builder::vip_ps(SETUP_RETRY_GAP);
        end
      end
    end
  endfunction

  virtual function void post_usb_20_packet_in_port_get(
      svt_usb_protocol component, int chan_id, svt_usb_packet packet, ref bit drop);
    bit [3:0] original_pid_check;
    if (!configured || checked || !pending_setup) return;
    if (packet == null) `uvm_fatal("OCP_SETUP_RETRY", "Null host receive packet")
    if (packet.pid_name != svt_usb_packet::ACK) return;
    pending_setup = 0;
    if (rejected_acks != 0) return;
    if (drop) `uvm_fatal("OCP_SETUP_RETRY", "Peer SETUP ACK was already dropped")
    // USB 2.0 8.3.1/8.6.4: an invalid ACK PID requires retransmission.
    // Use the VIP receive exception without discarding its completion channel.
    // The independent wire monitor retains the DUT's actual valid ACK.
    original_pid_check = packet.get_pid_check_val();
    if (original_pid_check !== ACK_PID_CHECK ||
        packet.get_pid_name_val() != svt_usb_packet::ACK)
      `uvm_fatal("OCP_SETUP_RETRY", "Selected wire ACK already contains a PID error")
    expected_reporter = component;
    injected_packet = packet;
    expected_error_armed = 1;
    super.post_usb_20_packet_in_port_get(component,chan_id,packet,drop);
    if (drop || packet.get_pid_check_val() === original_pid_check)
      `uvm_fatal("OCP_SETUP_RETRY", "VIP did not inject the selected ACK PID error")
    rejected_acks++;
    injection_confirmed = 1;
    `uvm_info("OCP_SETUP_RETRY",$sformatf(
      "Invalidated one received peer SETUP ACK PID address=%0d; canonical wire observation unchanged",
      address),UVM_NONE)
  endfunction

  virtual function void transaction_ended(svt_usb_protocol component,
      svt_usb_transfer transfer, int transaction_ix);
    if (transfer == native_transfer && transaction_ix == selected_transaction_ix)
      expected_error_armed = 0;
  endfunction

  virtual function void transfer_ended(svt_usb_protocol component,
      svt_usb_transfer transfer);
    if (transfer == native_transfer) expected_error_armed = 0;
  endfunction

  function void ocp_check_retry();
    if (!configured || checked || native_transfer == null ||
        setup_tokens != (extra_pid_mode == "repeat" ? 3 : 2) ||
        rejected_acks != 1 || expected_errors != 1)
      `uvm_fatal("OCP_SETUP_RETRY",$sformatf(
        "Peer SETUP replay incomplete configured=%0b checked=%0b tokens=%0d rejected_acks=%0d expected_errors=%0d",
        configured,checked,setup_tokens,rejected_acks,expected_errors))
    expected_error_armed = 0;
    checked = 1;
    `uvm_info("OCP_SETUP_RETRY",$sformatf(
      "Peer control completed after SETUP replay address=%0d native_instance=%0d tokens=%0d rejected_acks=%0d",
      address,native_transfer.get_inst_id(),setup_tokens,rejected_acks),UVM_NONE)
  endfunction
endclass
