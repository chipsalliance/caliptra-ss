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

// Corrupts the CRC16 of exactly one DATA1 OUT packet of the selected native
// control write, using the SVT packet-exception pattern from the vendor
// tb_usb_svt_uvm_20_phy CRC16 example restricted to the registered transfer.
class usb_ocp_write_crc_callback extends svt_usb_protocol_callback;
  `uvm_object_utils(usb_ocp_write_crc_callback)
  svt_usb_transfer target;
  bit injected;

  function new(string name = "usb_ocp_write_crc_callback");
    super.new(name);
  endfunction

  virtual function void pre_usb_20_packet_out_port_put(
      svt_usb_protocol component, int chan_id, svt_usb_packet packet,
      svt_usb_transaction transaction, int packet_ix,
      svt_usb_transfer transfer, int transaction_ix, ref bit drop);
    svt_usb_packet_exception exception;
    if (drop || injected || target == null || packet == null ||
        transfer != target || transaction == null ||
        transaction.get_xact_type_val() != svt_usb_types::OUT_TRANSACTION ||
        packet.pid_type != svt_usb_packet::DATA ||
        packet.get_pid_name_val() != svt_usb_packet::DATA1)
      return;
    exception = new();
    exception.xact = new();
    exception.error_kind = svt_usb_packet_exception::CRC_ERROR;
    exception.crc_error = svt_usb_packet_exception::CRC16_ERROR;
    if (packet.exception_list == null) packet.exception_list = new();
    packet.exception_list.add_exception(exception);
    injected = 1;
    `uvm_info("OCP_CRC_INJECTION", $sformatf(
      "Corrupting CRC16 of OCP write DATA1 dev=%0d wLength=%0d",
      transfer.device_address,transfer.setup_data_w_length),UVM_NONE)
  endfunction
endclass
