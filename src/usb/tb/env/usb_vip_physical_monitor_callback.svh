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

// The remote device PHY reports RX toward the DUT and TX from the DUT.
class usb_vip_physical_monitor_callback extends svt_usb_physical_monitor_callback;
  `uvm_object_utils(usb_vip_physical_monitor_callback)

  uvm_event out_token_event;
  uvm_event data_started_event;
  uvm_event rx_data_ended_event;
  uvm_event tx_data_ended_event;
  protected usb_vip_packet rx_packet;
  protected usb_vip_packet tx_packet;
  protected usb_vip_packet rx_data_packets[$];
  protected usb_vip_packet tx_data_packets[$];
  protected realtime rx_byte_times[$];
  protected realtime tx_byte_times[$];

  function new(string name = "usb_vip_physical_monitor_callback");
    super.new(name);
    out_token_event = new("out_token_event");
    data_started_event = new("data_started_event");
    rx_data_ended_event = new("rx_data_ended_event");
    tx_data_ended_event = new("tx_data_ended_event");
  endfunction

  function void clear_packets();
    rx_data_packets.delete();
    tx_data_packets.delete();
    out_token_event.reset();
    data_started_event.reset();
    rx_data_ended_event.reset();
    tx_data_ended_event.reset();
  endfunction

  task wait_for_data_packet(
    bit from_device,
    time timeout,
    output usb_vip_packet packet
  );
    bit observed;

    packet = null;
    observed = 1'b0;
    fork
      begin
        fork
          begin
            wait (from_device ? tx_data_packets.size() != 0 :
                                rx_data_packets.size() != 0);
            observed = 1'b1;
          end
          begin
            #(timeout);
          end
        join_any
        disable fork;
      end
    join
    if (!observed) begin
      `uvm_fatal("USB_VIP_PHY_MON", $sformatf("No %s DATA packet within %0t", from_device ? "device" : "host", timeout))
      return;
    end
    if (from_device) packet = tx_data_packets.pop_front();
    else packet = rx_data_packets.pop_front();
  endtask

  virtual task data_ended(
    svt_usb_physical_monitor physical_mon,
    svt_usb_data data
  );
    usb_vip_packet packet;
    bit from_device;

    if (data == null) begin
      `uvm_fatal("USB_VIP_PHY_MON", "VIP physical monitor supplied a null byte descriptor")
      return;
    end
    if (!data.is_byte_data) return;
    from_device = data.direction == svt_usb_data::TX;
    if (!(data.direction inside {svt_usb_data::RX, svt_usb_data::TX})) begin
      `uvm_fatal("USB_VIP_PHY_MON", "Unexpected remote PHY byte direction")
      return;
    end
    if (data.is_sop) begin
      packet = usb_vip_packet::type_id::create("observed_packet");
      packet.observed_at = $realtime;
      if (from_device) begin
        if (tx_packet != null) begin
          `uvm_fatal("USB_VIP_PHY_MON", "Device SOP preceded the previous EOP")
        end
        tx_packet = packet;
        tx_byte_times.delete();
      end else begin
        if (rx_packet != null) begin
          `uvm_fatal("USB_VIP_PHY_MON", "Host SOP preceded the previous EOP")
        end
        rx_packet = packet;
        rx_byte_times.delete();
      end
    end
    packet = from_device ? tx_packet : rx_packet;
    if (packet == null) begin
      `uvm_fatal("USB_VIP_PHY_MON", "VIP byte arrived without SOP")
      return;
    end
    packet.bytes.push_back(data.data);
    if (from_device) tx_byte_times.push_back($realtime);
    else rx_byte_times.push_back($realtime);
    if (!from_device && data.is_sop) begin
      if (data.data == 8'he1) out_token_event.trigger();
      if (packet.is_data()) data_started_event.trigger();
    end
    if (!data.is_eop) return;
    packet.completed_at = $realtime;
    if (packet.is_data()) begin
      if (packet.bytes.size() < 3) begin
        `uvm_fatal("USB_VIP_PHY_MON", "DATA packet is missing its CRC16")
        return;
      end
      // The final two descriptors carry the received CRC, not payload.
      packet.payload_completed_at = from_device ?
          tx_byte_times[packet.bytes.size() - 3] :
          rx_byte_times[packet.bytes.size() - 3];
      if (from_device) begin
        tx_data_packets.push_back(packet);
        tx_data_ended_event.trigger(packet);
      end else begin
        rx_data_packets.push_back(packet);
        rx_data_ended_event.trigger(packet);
      end
    end
    if (from_device) tx_packet = null;
    else rx_packet = null;
  endtask
endclass
