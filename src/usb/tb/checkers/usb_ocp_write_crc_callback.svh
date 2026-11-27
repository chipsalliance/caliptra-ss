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

// Reject the selected handshake at host receive without removing the
// completion descriptor or altering the DUT handshake on the wire.
class usb_ocp_write_crc_callback extends svt_usb_protocol_20_host_rx_pid_check_error;
  `uvm_object_utils(usb_ocp_write_crc_callback)
  svt_usb_transfer target;
  svt_usb_protocol reporter;
  bit injected;
  bit retry_crc;
  bit read_status_crc;
  bit loss_applied;
  bit clean_sent;
  bit out_context;
  bit awaiting_handshake;
  bit timeout_armed;
  bit timeout_seen;
  bit link_timeout_seen;
  int channel;
  int transaction_index = -1;
  int loss_index = -1;
  int fault_index = -1;

  function new(string name = "usb_ocp_write_crc_callback");
    super.new(name);
  endfunction

  virtual function void pre_usb_20_packet_out_port_put(
      svt_usb_protocol component, int chan_id, svt_usb_packet packet,
      svt_usb_transaction transaction, int packet_ix,
      svt_usb_transfer transfer, int transaction_ix, ref bit drop);
    svt_usb_packet_exception exception;
    if (target == null || packet == null || component != reporter) return;
    if (packet.pid_type == svt_usb_packet::TOKEN &&
        packet.get_pid_name_val() != svt_usb_packet::SOF) begin
      awaiting_handshake = 0;
      timeout_armed = 0;
      timeout_seen = 0;
      out_context = !drop && transfer == target && transaction != null &&
        packet.get_pid_name_val() == svt_usb_packet::OUT &&
        packet.device_address === target.device_address && packet.ept_num === 0;
      channel = chan_id;
      transaction_index = transaction_ix;
    end
    if (drop || !out_context || chan_id != channel || transaction_ix != transaction_index ||
        transfer != target || transaction == null ||
        transaction.get_xact_type_val() != (read_status_crc ?
          svt_usb_types::STATUS_TRANSACTION : svt_usb_types::OUT_TRANSACTION) ||
        packet.pid_type != svt_usb_packet::DATA ||
        packet.get_pid_name_val() != svt_usb_packet::DATA1)
      return;
    if (packet.get_payload_byte_count() != (read_status_crc ? 0 : 4))
      `uvm_fatal("OCP_CRC_SCOPE", "Selected DATA1 has the wrong stage length")
    if (retry_crc && !loss_applied) begin
      awaiting_handshake = 1;
      return;
    end
    if (retry_crc && transaction_ix != loss_index)
      `uvm_fatal("OCP_CRC_SCOPE", "OUT retry did not preserve the native transaction index")
    if (injected) begin
      if (transaction_ix != fault_index)
        `uvm_fatal("OCP_CRC_SCOPE", "Clean retry did not preserve the native transaction index")
      clean_sent = 1;
      return;
    end
    exception = new();
    exception.xact = new();
    exception.error_kind = svt_usb_packet_exception::CRC_ERROR;
    exception.crc_error = svt_usb_packet_exception::CRC16_ERROR;
    if (packet.exception_list == null) packet.exception_list = new();
    packet.exception_list.add_exception(exception);
    injected = 1;
    fault_index = transaction_ix;
    timeout_armed = 1;
    `uvm_info("OCP_CRC_INJECTION", $sformatf(
      "CRC16 injected addr=%0d native=%0d transaction=%0d read_status=%0b after_loss=%0b",
      transfer.device_address,transfer.get_inst_id(),fault_index,read_status_crc,loss_applied),UVM_NONE)
  endfunction

  virtual function void post_usb_20_packet_in_port_get(
      svt_usb_protocol component, int chan_id, svt_usb_packet packet, ref bit drop);
    svt_usb_packet::pid_name_enum pid;
    bit [3:0] original_check;
    if (!awaiting_handshake || !retry_crc || loss_applied || target == null ||
        component != reporter || packet == null ||
        packet.pid_type != svt_usb_packet::HANDSHAKE)
      return;
    awaiting_handshake = 0;
    pid = packet.get_pid_name_val();
    if (!(pid inside {svt_usb_packet::ACK,svt_usb_packet::NYET})) return;
    // USB 2.0 Table 8-1: validate the ACK/NYET PID complement before loss.
    original_check = packet.get_pid_check_val();
    if (drop || original_check !== (pid == svt_usb_packet::ACK ? 4'hd : 4'h9))
      `uvm_fatal("OCP_CRC_LOSS", "Expected a valid, not-yet-dropped OUT ACK/NYET")
    loss_applied = 1;
    loss_index = transaction_index;
    super.post_usb_20_packet_in_port_get(component,chan_id,packet,drop);
    if (drop || packet.get_pid_check_val() === original_check)
      `uvm_fatal("OCP_CRC_LOSS", "VIP did not invalidate the selected receive PID check")
    `uvm_info("OCP_CRC_LOSS",$sformatf(
      "Invalidated host receive PID check pid=%s addr=%0d native=%0d transaction=%0d tx_chan=%0d rx_chan=%0d",
      packet.pid_name.name(),target.device_address,target.get_inst_id(),loss_index,channel,chan_id),UVM_NONE)
  endfunction

  virtual function void transaction_ended(svt_usb_protocol component,
      svt_usb_transfer transfer, int transaction_ix);
    if (component == reporter && transfer == target && transaction_ix == transaction_index)
      awaiting_handshake = 0;
  endfunction

  virtual function void transfer_ended(svt_usb_protocol component, svt_usb_transfer transfer);
    if (component == reporter && transfer == target) begin
      awaiting_handshake = 0;
      timeout_armed = 0;
      out_context = 0;
    end
  endfunction
endclass
