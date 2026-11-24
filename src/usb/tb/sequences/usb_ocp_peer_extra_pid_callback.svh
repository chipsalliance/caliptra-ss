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

class usb_ocp_peer_extra_pid_callback extends svt_usb_protocol_20_host_rx_pid_check_error;
  `uvm_object_utils(usb_ocp_peer_extra_pid_callback)
  usb_ocp_peer_setup_retry_callback control;
  svt_usb_transfer extra_transfer;
  bit pending_ack;
  int unsigned setup_tokens;

  function new(string name = "usb_ocp_peer_extra_pid_callback");
    super.new(name);
  endfunction

  virtual function void pre_usb_20_packet_out_port_put(
      svt_usb_protocol component, int chan_id, svt_usb_packet packet,
      svt_usb_transaction transaction, int packet_ix,
      svt_usb_transfer transfer, int transaction_ix, ref bit drop);
    if (packet == null || packet.pid_type != svt_usb_packet::TOKEN ||
        packet.pid_name == svt_usb_packet::SOF)
      return;
    pending_ack = 0;
    if (drop || control.expected_errors != 1 || transfer == null ||
        packet.pid_name != svt_usb_packet::SETUP ||
        packet.device_address !== control.address || packet.ept_num !== 0)
      return;
    if ((control.extra_pid_mode == "repeat" && transfer == control.native_transfer) ||
        (control.extra_pid_mode == "unrelated" && control.checked &&
         transfer != control.native_transfer &&
         transfer.setup_data_brequest == svt_usb_types::GET_DESCRIPTOR)) begin
      if (extra_transfer == null) extra_transfer = transfer;
      if (transfer != extra_transfer) return;
      setup_tokens++;
      if (setup_tokens > 1)
        packet.inter_pkt_usb_20_diff_source_delay =
          usb_vip_cfg_builder::vip_ps(usb_ocp_peer_setup_retry_callback::SETUP_RETRY_GAP);
      pending_ack = control.extra_pid_injections == 0;
    end
  endfunction

  virtual function void post_usb_20_packet_in_port_get(
      svt_usb_protocol component, int chan_id, svt_usb_packet packet, ref bit drop);
    bit [3:0] original_pid_check;
    if (!pending_ack || packet == null || packet.pid_name != svt_usb_packet::ACK)
      return;
    pending_ack = 0;
    if (drop) `uvm_fatal("OCP_SETUP_RETRY_CANARY", "Canary ACK was already dropped")
    original_pid_check = packet.get_pid_check_val();
    if (original_pid_check !== usb_ocp_peer_setup_retry_callback::ACK_PID_CHECK ||
        packet.get_pid_name_val() != svt_usb_packet::ACK)
      `uvm_fatal("OCP_SETUP_RETRY_CANARY", "Canary wire ACK already contains a PID error")
    // Re-arm the documented one-shot injector for a second native packet.
    // No expected-error window is opened for this canary.
    packet_count = 0;
    super.post_usb_20_packet_in_port_get(component,chan_id,packet,drop);
    if (drop || packet.get_pid_check_val() === original_pid_check)
      `uvm_fatal("OCP_SETUP_RETRY_CANARY", "Second native PID-error injection did not occur")
    control.extra_pid_injections++;
    `uvm_info("OCP_SETUP_RETRY_CANARY",$sformatf(
      "Injected unsuppressed %s native SETUP ACK PID error",control.extra_pid_mode),UVM_NONE)
  endfunction
endclass
