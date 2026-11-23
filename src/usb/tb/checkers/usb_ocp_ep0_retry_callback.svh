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

class usb_ocp_ep0_retry_callback extends svt_usb_protocol_callback;
  `uvm_object_utils(usb_ocp_ep0_retry_callback)
  usb_ocp_ep0_retry_control control;
  bit out_wait;
  svt_usb_transaction out_transaction;
  int out_transaction_ix = -1;
  bit read_wait;
  bit read_response_armed;
  bit read_data_received;
  svt_usb_transaction read_transaction;
  int read_transaction_ix = -1;

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
      read_wait = 0;
    end
    if (!drop && control.original != null && transfer == control.original &&
        control.kind == usb_ocp_ep0_retry_control::READ_RETRY &&
        transaction != null && packet.pid_type == svt_usb_packet::TOKEN &&
        packet.get_pid_name_val() == svt_usb_packet::IN) begin
      if (read_transaction != transaction) read_response_armed = 0;
      read_transaction = transaction;
      read_transaction_ix = transaction_ix;
      read_data_received = 0;
      read_wait = 1;
    end
    if (drop || control.original == null ||
        control.kind != usb_ocp_ep0_retry_control::WRITE_RETRY ||
        control.loss_applied || transfer != control.original || transaction == null)
      return;
    if (transaction.get_xact_type_val() == svt_usb_types::OUT_TRANSACTION &&
        packet.pid_type == svt_usb_packet::DATA &&
        packet.get_pid_name_val() == svt_usb_packet::DATA1) begin
      out_wait = 1;
      out_transaction = transaction;
      out_transaction_ix = transaction_ix;
    end
  endfunction

  // Drop at the host's protocol input, after wire observation but before
  // accepting ACK/NYET. USB 2.0 8.6.4 requires retransmission, not a new SETUP.
  virtual function void post_usb_20_packet_in_port_get(
      svt_usb_protocol component, int chan_id, svt_usb_packet packet, ref bit drop);
    if (read_wait && control.original != null &&
        control.kind == usb_ocp_ep0_retry_control::READ_RETRY &&
        packet != null && !drop && !control.loss_applied) begin
      if (packet.pid_type == svt_usb_packet::DATA) begin
        read_data_received = 1;
        ocp_confirm_read_loss();
      end else if (packet.pid_type == svt_usb_packet::HANDSHAKE)
        read_data_received = 0;
      return;
    end
    if (!out_wait || control.original == null || control.loss_applied ||
        packet == null || drop || packet.pid_type != svt_usb_packet::HANDSHAKE)
      return;
    out_wait = 0;
    if (packet.get_pid_name_val() inside {svt_usb_packet::ACK,svt_usb_packet::NYET}) begin
      if (!control.skip_loss) begin
        control.expected_timeout_armed = 1;
        drop = 1;
        control.ocp_record_loss(out_transaction,out_transaction_ix);
        `uvm_info("OCP_EP0_RETRY_LOSS", "Host protocol discards one received OUT ACK/NYET", UVM_NONE)
      end
    end
  endfunction

  function void ocp_confirm_read_loss();
    if (!read_response_armed || !read_data_received || control.loss_applied)
      return;
    control.ocp_record_loss(read_transaction,read_transaction_ix);
    `uvm_info("OCP_EP0_RETRY_LOSS", "Host omits one ACK after actual selected IN DATA", UVM_NONE)
  endfunction

  virtual function void transaction_ended(svt_usb_protocol component,
      svt_usb_transfer transfer, int transaction_ix);
    if (transfer == control.original && transaction_ix == read_transaction_ix) begin
      read_wait = 0;
      read_response_armed = 0;
      read_data_received = 0;
      read_transaction = null;
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
    if (read_transaction != transaction) read_data_received = 0;
    read_transaction = transaction;
    read_transaction_ix = transaction_ix;
    read_response_armed = wanted == svt_usb_transaction::HOST_TIMEOUT_RESPONSE;
    if (wanted == svt_usb_transaction::HOST_TIMEOUT_RESPONSE) begin
      ocp_confirm_read_loss();
    end
  endfunction
endclass
