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

// Extends enumeration with one unsupported request and protocol STALL check.
class usb_unsupported_request_seq extends usb_init_seq;
  `uvm_object_utils(usb_unsupported_request_seq)

  function new(string name = "usb_unsupported_request_seq");
    super.new(name);
  endfunction

  virtual function int unsigned expected_setup_request_count();
    return 8;
  endfunction

  // Stall both EP0 directions for the eighth unsupported request.
  virtual task service_setup_request();
    byte unsigned request_type;
    byte unsigned request;
    logic [15:0] value;
    logic [15:0] index;
    logic [15:0] length;

    if (serviced_request_count < 7) begin
      super.service_setup_request();
      return;
    end

    read_setup_packet(request_type, request, value, index, length);
    if (request_type != 8'h00 || request != 8'h7f || length != 4) begin
      `uvm_fatal("USB_UNSUPPORTED_SEQ", $sformatf("Unexpected final SETUP: type=0x%02h request=0x%02h length=%0d", request_type, request, length))
    end
    write_endpoint_entry(ep0_in_endpoint, endpoint_entry(1'b0, 1'b1, 0, ep0_in_buffer_offset));
    write_endpoint_entry(ep0_out_endpoint, endpoint_entry(1'b0, 1'b1, 0, ep0_out_buffer_offset));
    clear_setup_bit();
    serviced_request_count++;
    `uvm_info("USB_UNSUPPORTED_SEQ", "Armed EP0 IN and OUT STALL responses for unsupported request 0x7f", UVM_LOW)
  endtask

  // Run normal enumeration followed by the unsupported request.
  virtual task run_host_scenario();
    usb_init_host_seq init_host_sequence;
    usb_unsupported_request_host_seq unsupported_host_sequence;
    int unsigned stall_count;

    host_scenario_completed = 1'b0;
    init_host_sequence = usb_init_host_seq::type_id::create("init_host_sequence");
    init_host_sequence.control_endpoint = ep0_out_endpoint;
    init_host_sequence.device_address = p_sequencer.cfg.device_address;
    init_host_sequence.link_timeout = p_sequencer.cfg.link_timeout;
    init_host_sequence.control_transfer_timeout = p_sequencer.cfg.control_transfer_timeout;
    init_host_sequence.start(p_sequencer.host_sequencer);
    if (!init_host_sequence.completed) begin
      `uvm_fatal("USB_UNSUPPORTED_SEQ", "Enumeration host sequence returned incomplete")
    end

    unsupported_host_sequence = usb_unsupported_request_host_seq::type_id::create("unsupported_host_sequence");
    unsupported_host_sequence.control_endpoint = ep0_out_endpoint;
    unsupported_host_sequence.device_address = p_sequencer.cfg.device_address;
    unsupported_host_sequence.control_transfer_timeout = p_sequencer.cfg.control_transfer_timeout;

    p_sequencer.packet_monitor.start_window("Unsupported control request STALL");
    unsupported_host_sequence.start(p_sequencer.host_sequencer);
    p_sequencer.packet_monitor.stop_window();
    if (!unsupported_host_sequence.completed) begin
      `uvm_fatal("USB_UNSUPPORTED_SEQ", "Unsupported-request host sequence returned incomplete")
    end
    stall_count = p_sequencer.packet_monitor.count_pid(
      svt_usb_packet::STALL,
      usb_packet_monitor_callback::USB_PACKET_RX
    );
    if (stall_count == 0) begin
      `uvm_fatal("USB_UNSUPPORTED_SEQ", "No device STALL packet was observed for the unsupported request")
    end

    host_scenario_completed = 1'b1;
    `uvm_info("USB_UNSUPPORTED_SEQ", $sformatf("Unsupported request produced %0d observed device STALL packet(s)", stall_count), UVM_LOW)
  endtask
endclass
