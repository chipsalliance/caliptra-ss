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

// Synopsys USB VIP UVM Class Reference:
// Paths are relative to doc/class_ref/usb_svt_uvm_class_reference/html/.
// callback/class_svt_usb_link_monitor_callback.html,
// usb_20_rx_packet_ended() / usb_20_tx_packet_ended(): completed packet hooks.
// Register on host_agent.link_mon. RX is from the DUT, TX from the host.
// A sequence starts a window before stimulus, waits for protocol traffic to
// drain, stops the window, then queries counts/retry evidence. One sequence
// owns the window at a time. Only decoded fields are copied; the VIP packet,
// protocol processing, and built-in checks are not modified or bypassed.
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
  protected uvm_event ping_observed;
  protected uvm_event sof_observed;
  protected bit sof_seen_in_window;

  function new(string name = "usb_packet_monitor_callback");
    super.new(name);
    ping_observed = new("ping_observed");
    sof_observed = new("sof_observed");
  endfunction

  // Start a fresh observation window before scenario stimulus.
  function void start_window(string label);
    if (window_active) begin
      `uvm_fatal("USB_PACKET_MON", $sformatf("Cannot start %s while %s is active", label, window_label))
    end
    records.delete();
    window_label = label;
    ping_observed.reset();
    sof_observed.reset();
    sof_seen_in_window = 1'b0;
    window_active = 1'b1;
    `uvm_info("USB_PACKET_MON", $sformatf("Started packet observation window: %s", window_label), UVM_LOW)
  endfunction

  // Wait for a host PING packet during the active observation window.
  task wait_for_ping(time timeout, output bit observed);
    observed = 1'b0;
    if (!window_active) begin
      `uvm_fatal("USB_PACKET_MON", "PING wait requires an active observation window")
    end
    fork
      begin
        ping_observed.wait_trigger();
        observed = 1'b1;
      end
      begin
        #(timeout);
      end
    join_any
    disable fork;
  endtask

  // Wait for a host SOF packet during the active observation window.
  task wait_for_sof(time timeout, output bit observed);
    observed = sof_seen_in_window;
    if (!window_active) begin
      `uvm_fatal("USB_PACKET_MON", "SOF wait requires an active observation window")
    end
    if (observed) return;
    // Isolate cancellation from VIP workers started by the calling sequence.
    fork
      begin
        fork
          begin
            sof_observed.wait_ptrigger();
            observed = 1'b1;
          end
          begin
            #(timeout);
          end
        join_any
        disable fork;
      end
    join
  endtask

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

  function void get_records(output usb_packet_record_t observed_records[$]);
    if (window_active) begin
      `uvm_fatal("USB_PACKET_MON", "Close the observation window before copying packet records")
    end
    observed_records = records;
  endfunction

  // USB 2.0 Section 8.5.1: ACK and NYET both accept high-speed OUT data.
  function bit observed_rejected_out_retry(
    bit [6:0] device_address,
    bit [3:0] endpoint_number,
    output int unsigned attempt_count
  );
    bit data_seen;
    bit first_attempt_accepted;
    bit retry_accepted;

    attempt_count = 0;
    data_seen = 1'b0;
    first_attempt_accepted = 1'b0;
    retry_accepted = 1'b0;
    foreach (records[index]) begin
      if (records[index].direction == USB_PACKET_TX &&
          records[index].pid_name == svt_usb_packet::OUT &&
          records[index].device_address == device_address &&
          records[index].endpoint_number == endpoint_number) begin
        attempt_count++;
        data_seen = 1'b0;
        continue;
      end
      if (attempt_count != 0 &&
          records[index].direction == USB_PACKET_TX &&
          (records[index].pid_name == svt_usb_packet::DATA0 ||
           records[index].pid_name == svt_usb_packet::DATA1)) begin
        data_seen = 1'b1;
        continue;
      end
      if (data_seen &&
          records[index].direction == USB_PACKET_RX &&
          (records[index].pid_name == svt_usb_packet::ACK ||
           records[index].pid_name == svt_usb_packet::NYET)) begin
        if (attempt_count == 1) begin
          first_attempt_accepted = 1'b1;
        end else begin
          retry_accepted = 1'b1;
        end
        data_seen = 1'b0;
      end
    end
    return attempt_count >= 2 && !first_attempt_accepted && retry_accepted;
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
    if (direction == USB_PACKET_TX && packet.pid_name == svt_usb_packet::PING) begin
      ping_observed.trigger();
    end
    if (direction == USB_PACKET_TX && packet.pid_name == svt_usb_packet::SOF) begin
      sof_seen_in_window = 1'b1;
      sof_observed.trigger();
    end
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
