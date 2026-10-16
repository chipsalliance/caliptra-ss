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

// Selects one-shot host token CRC5 corruption for the shared CRC scenario.
class usb_bad_crc5_seq extends usb_bad_packet_crc_seq;
  `uvm_object_utils(usb_bad_crc5_seq)

  svt_usb_protocol_20_host_tx_packet_crc5_error crc5_callback;

  function new(string name = "usb_bad_crc5_seq");
    super.new(name);
  endfunction

  virtual function logic [3:0] expected_error_code();
    return 4'h4;
  endfunction

  virtual function string scenario_label();
    return "bad token CRC5";
  endfunction

  virtual task install_injection(svt_usb_agent host_agent);
    svt_usb_protocol_20_host_tx_packet_crc5_error::packet_count = 0;
    crc5_callback = svt_usb_protocol_20_host_tx_packet_crc5_error::type_id::create("crc5_callback");
    uvm_callbacks#(svt_usb_protocol, svt_usb_protocol_callbacks)::add(host_agent.prot, crc5_callback);
  endtask

  virtual task remove_injection(svt_usb_agent host_agent);
    uvm_callbacks#(svt_usb_protocol, svt_usb_protocol_callbacks)::delete(host_agent.prot, crc5_callback);
  endtask

  virtual function int unsigned injected_packet_count();
    return svt_usb_protocol_20_host_tx_packet_crc5_error::packet_count;
  endfunction
endclass
