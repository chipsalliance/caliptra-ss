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

// Selects one-shot host data CRC16 corruption for the shared CRC scenario.
class usb_bad_crc16_seq extends usb_bad_packet_crc_seq;
  `uvm_object_utils(usb_bad_crc16_seq)

  svt_usb_protocol_20_host_tx_packet_crc16_error crc16_callback;

  function new(string name = "usb_bad_crc16_seq");
    super.new(name);
    payload_base = 8'h70;
  endfunction

  virtual function logic [3:0] expected_error_code();
    return 4'h5;
  endfunction

  virtual function string scenario_label();
    return "bad data CRC16";
  endfunction

  virtual task install_injection(svt_usb_agent host_agent);
    svt_usb_protocol_20_host_tx_packet_crc16_error::packet_count = 0;
    crc16_callback = svt_usb_protocol_20_host_tx_packet_crc16_error::type_id::create("crc16_callback");
    uvm_callbacks#(svt_usb_protocol, svt_usb_protocol_callback)::add(host_agent.prot, crc16_callback);
  endtask

  virtual task remove_injection(svt_usb_agent host_agent);
    uvm_callbacks#(svt_usb_protocol, svt_usb_protocol_callback)::delete(host_agent.prot, crc16_callback);
  endtask

  virtual function int unsigned injected_packet_count();
    return svt_usb_protocol_20_host_tx_packet_crc16_error::packet_count;
  endfunction
endclass
