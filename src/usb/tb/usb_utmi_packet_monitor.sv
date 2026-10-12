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

// Reconstructs complete host and device UTMI packets and publishes events.
module usb_utmi_packet_monitor (
  input logic       clk,
  input logic       reset_n,
  input logic       rxactive,
  input logic       rxvalid,
  input logic [7:0] rxdata,
  input logic       txvalid,
  input logic       txready,
  input logic [7:0] txdata
);
  import uvm_pkg::*;
  import usb_tb_pkg::*;

  localparam logic [7:0] USB_PID_OUT = 8'he1;
  localparam logic [7:0] USB_PID_DATA0 = 8'hc3;
  localparam logic [7:0] USB_PID_DATA1 = 8'h4b;
  localparam logic [7:0] USB_PID_DATA2 = 8'h87;
  localparam logic [7:0] USB_PID_MDATA = 8'h0f;

  logic packet_started;
  logic rx_packet_active;
  logic tx_packet_active;
  uvm_event out_token_event;
  uvm_event data_packet_event;
  uvm_event rx_data_packet_event;
  uvm_event tx_packet_event;
  usb_utmi_packet rx_packet;
  usb_utmi_packet tx_packet;
  int unsigned out_token_count;
  int unsigned data_packet_count;
  int unsigned rx_data_packet_count;
  int unsigned tx_packet_count;

  initial begin
    out_token_event = uvm_event_pool::get_global(USB_UTMI_OUT_TOKEN_EVENT);
    data_packet_event = uvm_event_pool::get_global(USB_UTMI_DATA_PACKET_EVENT);
    rx_data_packet_event =
        uvm_event_pool::get_global(USB_UTMI_RX_DATA_PACKET_EVENT);
    tx_packet_event = uvm_event_pool::get_global(USB_UTMI_TX_PACKET_EVENT);
    `uvm_info("USB_UTMI_MON", "Passive UTMI packet monitor started", UVM_LOW)
  end

  // Reconstruct packets and publish packet-start compatibility events.
  always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      packet_started <= 1'b0;
      rx_packet_active <= 1'b0;
      tx_packet_active <= 1'b0;
      rx_packet = null;
      tx_packet = null;
      out_token_count <= 0;
      data_packet_count <= 0;
      rx_data_packet_count <= 0;
      tx_packet_count <= 0;
    end else if (!rxactive) begin
      packet_started <= 1'b0;
    end else if (rxvalid && !packet_started) begin
      packet_started <= 1'b1;
      if (rxdata === USB_PID_OUT) begin
        out_token_count <= out_token_count + 1;
        out_token_event.trigger();
      end
      if (rxdata inside {
            USB_PID_DATA0,
            USB_PID_DATA1,
            USB_PID_DATA2,
            USB_PID_MDATA
          }) begin
        data_packet_count <= data_packet_count + 1;
        data_packet_event.trigger();
      end
    end

    if (reset_n && rxactive && rxvalid) begin
      if (!rx_packet_active) begin
        rx_packet = usb_utmi_packet::type_id::create(
            $sformatf("rx_packet_%0d", rx_data_packet_count + 1));
        rx_packet.observed_at = $realtime;
        rx_packet_active <= 1'b1;
      end
      rx_packet.bytes.push_back(rxdata);
    end else if (reset_n && !rxactive && rx_packet_active) begin
      rx_packet_active <= 1'b0;
      if (rx_packet.bytes[0] inside {
            USB_PID_DATA0,
            USB_PID_DATA1,
            USB_PID_DATA2,
            USB_PID_MDATA
          }) begin
        rx_data_packet_count <= rx_data_packet_count + 1;
        rx_data_packet_event.trigger(rx_packet);
      end
      rx_packet = null;
    end

    if (reset_n && txvalid && txready) begin
      if (!tx_packet_active) begin
        tx_packet = usb_utmi_packet::type_id::create(
            $sformatf("tx_packet_%0d", tx_packet_count + 1));
        tx_packet.observed_at = $realtime;
        tx_packet_active <= 1'b1;
      end
      tx_packet.bytes.push_back(txdata);
    end else if (reset_n && !txvalid && tx_packet_active) begin
      tx_packet_active <= 1'b0;
      tx_packet_count <= tx_packet_count + 1;
      tx_packet_event.trigger(tx_packet);
      tx_packet = null;
    end
  end
endmodule
