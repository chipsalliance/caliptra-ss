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

// Records packets from the passive SVT link monitor during bounded windows.
class usb_packet_monitor_callback extends svt_usb_link_monitor_callback;
  `uvm_object_utils(usb_packet_monitor_callback)

  typedef enum bit {
    USB_PACKET_RX,
    USB_PACKET_TX
  } usb_packet_direction_e;

  typedef struct {
    usb_packet_direction_e direction;
    svt_usb_packet::pid_name_enum pid_name;
    bit [6:0] device_address;
    bit [3:0] endpoint_number;
    int unsigned data_length;
    realtime observed_at;
  } usb_packet_record_t;

  protected usb_packet_record_t records[$];
  protected bit window_active;
  protected string window_label;

  function new(string name = "usb_packet_monitor_callback");
    super.new(name);
  endfunction

  // Start a fresh observation window before scenario stimulus.
  function void start_window(string label);
    if (window_active) begin
      `uvm_fatal("USB_PACKET_MON", $sformatf("Cannot start %s while %s is active", label, window_label))
    end
    records.delete();
    window_label = label;
    window_active = 1'b1;
    `uvm_info("USB_PACKET_MON", $sformatf("Started packet observation window: %s", window_label), UVM_LOW)
  endfunction

  // Close the active window after all relevant packets have drained.
  function void stop_window();
    if (!window_active) begin
      `uvm_fatal("USB_PACKET_MON", "Cannot stop a packet observation window that is not active")
    end
    window_active = 1'b0;
    `uvm_info("USB_PACKET_MON", $sformatf("Stopped packet observation window %s: packets=%0d", window_label, records.size()), UVM_LOW)
  endfunction

  // Count one packet PID in one observed direction.
  function int unsigned count_pid(
    svt_usb_packet::pid_name_enum pid_name,
    usb_packet_direction_e direction
  );
    int unsigned count;

    count = 0;
    foreach (records[index]) begin
      if (records[index].pid_name == pid_name &&
          records[index].direction == direction) begin
        count++;
      end
    end
    return count;
  endfunction

  // Capture one packet without driving or modifying link behavior.
  protected function void record_packet(
    usb_packet_direction_e direction,
    svt_usb_packet packet
  );
    usb_packet_record_t record;

    if (!window_active || packet == null) begin
      return;
    end
    record.direction = direction;
    record.pid_name = packet.pid_name;
    record.device_address = packet.get_device_address_val();
    record.endpoint_number = packet.ept_num;
    record.data_length = packet.get_payload_byte_count();
    record.observed_at = $realtime;
    records.push_back(record);
  endfunction

  virtual function void usb_20_rx_packet_ended(
    svt_usb_link_monitor link_mon,
    svt_usb_packet pkt
  );
    record_packet(USB_PACKET_RX, pkt);
  endfunction

  virtual function void usb_20_tx_packet_ended(
    svt_usb_link_monitor link_mon,
    svt_usb_packet pkt
  );
    record_packet(USB_PACKET_TX, pkt);
  endfunction
endclass
