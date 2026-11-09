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

// Sends one SVT USB 2.0 packet with an intentional PID_CHECK_ERROR exception
// (exception/class_svt_usb_packet_exception.html) on usb_20_pkt_sequencer.
class usb_bad_pid_packet_seq extends svt_usb_packet_base_sequence;
  `uvm_object_utils(usb_bad_pid_packet_seq)

  bit [6:0] device_address = USB_DEFAULT_DEVICE_ADDRESS;
  bit [3:0] endpoint_number = 4'd1;

  function new(string name = "usb_bad_pid_packet_seq");
    super.new(name);
  endfunction

  virtual task body();
    svt_usb_packet packet;
    svt_usb_packet_exception pid_exception;

    packet = new_item("bad_pid_in_token");
    packet.speed = svt_usb_types::HS;
    packet.payload = new("packet_payload");
    packet.payload_offset = 0;
    start_item(packet);
    if (!packet.randomize() with {
          pid_type == svt_usb_packet::TOKEN;
          pid_name == svt_usb_packet::IN;
          device_address == local::device_address;
          ept_num == local::endpoint_number;
          payload.byte_count == 0;
        }) begin
      `uvm_fatal("USB_BAD_PID_PKT", "Failed to randomize bad-PID IN token packet")
    end
    pid_exception = new("bad_pid_check");
    pid_exception.cfg = packet.cfg;
    pid_exception.xact = packet;
    pid_exception.error_group = svt_usb_packet_exception::RANDOM_ERROR_GROUP;
    pid_exception.error_kind = svt_usb_packet_exception::PID_CHECK_ERROR;
    pid_exception.mask_or_value = 32'h1;
    pid_exception.no_exception = 1'b0;
    pid_exception.recognized = 1'b0;
    if (packet.exception_list == null) begin
      packet.exception_list = new("packet_exceptions");
    end
    packet.exception_list.add_exception(pid_exception);
    finish_item(packet);
    if (!packet.end_is_on()) begin
      packet.wait_end();
    end
  endtask
endclass
