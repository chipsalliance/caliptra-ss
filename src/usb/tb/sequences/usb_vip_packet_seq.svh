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

// Directed USB 2.0 packet exceptions and manual ISO token/data scheduling.
// Start on host_sequencer.usb_20_pkt_sequencer, not the protocol sequencer.
// Callers must finish protocol traffic and stop automatic SOFs before a raw
// packet interval, then restore SOFs afterwards. Use protocol transfers for
// ordinary traffic so the VIP owns transaction scheduling and checking.
class usb_vip_packet_seq extends svt_usb_packet_base_sequence;
  `uvm_object_utils(usb_vip_packet_seq)

  svt_usb_packet::pid_name_enum packet_pid;
  bit [6:0] device_address = USB_DEFAULT_DEVICE_ADDRESS;
  bit [3:0] endpoint_number;
  bit [10:0] frame_number;
  byte unsigned payload_bytes[$];
  bit corrupt_pid_check;
  bit isochronous;
  time packet_timeout = 100us;

  function new(string name = "usb_vip_packet_seq");
    super.new(name);
  endfunction

  task body();
    svt_usb_packet packet;
    svt_usb_packet::pid_type_enum packet_type;
    svt_usb_packet_exception pid_exception;
    int unsigned payload_size;
    bit finished;

    packet_type = packet_pid inside {
        svt_usb_packet::DATA0, svt_usb_packet::DATA1,
        svt_usb_packet::DATA2, svt_usb_packet::MDATA
    } ? svt_usb_packet::DATA : svt_usb_packet::TOKEN;
    payload_size = payload_bytes.size();
    packet = new_item("host_packet");
    packet.speed = svt_usb_types::HS;
    packet.payload = new("packet_payload");
    packet.payload_offset = 0;
    start_item(packet);
    if (!packet.randomize() with {
          pid_type == local::packet_type;
          pid_name == local::packet_pid;
          device_address == local::device_address;
          ept_num == local::endpoint_number;
          frame_number == local::frame_number;
          payload.byte_count == local::payload_size;
          payload.data_generation_algorithm ==
              svt_usb_payload::USER_DEFINED_ALGORITHM;
        }) begin
      `uvm_fatal("USB_VIP_PACKET", "Unable to randomize the requested USB 2.0 packet")
    end
    foreach (payload_bytes[index]) begin
      packet.payload.data[index] = payload_bytes[index];
    end
    if (isochronous) begin
      packet.et = svt_usb_types::ISOCHRONOUS;
      packet.ep_type_valid = 1'b1;
      packet.ep_type_invalid = 1'b0;
    end
    if (corrupt_pid_check) begin
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
    end
    finished = 1'b0;
    fork
      begin
        fork
          begin
            finish_item(packet);
            if (!packet.end_is_on()) packet.wait_end();
            finished = 1'b1;
          end
          begin
            #(packet_timeout);
          end
        join_any
        disable fork;
      end
    join
    if (!finished) begin
      `uvm_fatal("USB_VIP_PACKET", $sformatf("%s did not complete within %0t", packet_pid.name(), packet_timeout))
    end
  endtask
endclass
