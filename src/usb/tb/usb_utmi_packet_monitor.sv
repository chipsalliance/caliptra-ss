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

// Publishes packet-start events from passively observed UTMI receive traffic.
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
  localparam logic [7:0] USB_PID_IN = 8'h69;
  localparam logic [7:0] USB_PID_DATA0 = 8'hc3;
  localparam logic [7:0] USB_PID_DATA1 = 8'h4b;
  localparam logic [7:0] USB_PID_DATA2 = 8'h87;
  localparam logic [7:0] USB_PID_MDATA = 8'h0f;

  logic packet_started;
  logic tx_packet_active;
  uvm_event out_token_event;
  uvm_event in_token_event;
  uvm_event data_packet_event;
  uvm_event tx_packet_event;
  uvm_event tx_data_progress_event;
  uvm_event tx_data_packet_event;
  usb_utmi_tx_packet tx_packet;
  int unsigned out_token_count;
  int unsigned in_token_count;
  int unsigned data_packet_count;
  int unsigned tx_packet_count;

  initial begin
    out_token_event = uvm_event_pool::get_global(USB_UTMI_OUT_TOKEN_EVENT);
    in_token_event = uvm_event_pool::get_global(USB_UTMI_IN_TOKEN_EVENT);
    data_packet_event = uvm_event_pool::get_global(USB_UTMI_DATA_PACKET_EVENT);
    tx_packet_event = uvm_event_pool::get_global(USB_UTMI_TX_PACKET_EVENT);
    tx_data_progress_event = uvm_event_pool::get_global(USB_UTMI_TX_DATA_PROGRESS_EVENT);
    tx_data_packet_event = uvm_event_pool::get_global(USB_UTMI_TX_DATA_PACKET_EVENT);
    `uvm_info("USB_UTMI_MON", "Passive UTMI packet monitor started", UVM_LOW)
  end

  // Recognize the first valid byte of each receive packet as its PID.
  always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      packet_started <= 1'b0;
      tx_packet_active <= 1'b0;
      tx_packet = null;
      out_token_count <= 0;
      in_token_count <= 0;
      data_packet_count <= 0;
      tx_packet_count <= 0;
    end else if (!rxactive) begin
      packet_started <= 1'b0;
    end else if (rxvalid && !packet_started) begin
      packet_started <= 1'b1;
      if (rxdata === USB_PID_OUT) begin
        out_token_count <= out_token_count + 1;
        out_token_event.trigger();
        `uvm_info("USB_UTMI_MON", $sformatf("Observed OUT token %0d", out_token_count + 1), UVM_HIGH)
      end
      if (rxdata === USB_PID_IN) begin
        in_token_count <= in_token_count + 1;
        in_token_event.trigger();
        `uvm_info("USB_UTMI_MON", $sformatf("Observed IN token %0d", in_token_count + 1), UVM_HIGH)
      end
      if (rxdata inside {USB_PID_DATA0, USB_PID_DATA1, USB_PID_DATA2, USB_PID_MDATA}) begin
        data_packet_count <= data_packet_count + 1;
        data_packet_event.trigger();
        `uvm_info("USB_UTMI_MON", $sformatf("Observed DATA packet %0d", data_packet_count + 1), UVM_HIGH)
      end
    end

    if (reset_n && txvalid && txready) begin
      if (!tx_packet_active) begin
        tx_packet = usb_utmi_tx_packet::type_id::create($sformatf("tx_packet_%0d", tx_packet_count + 1));
        tx_packet.observed_at = $realtime;
        tx_packet_active <= 1'b1;
      end
      tx_packet.bytes.push_back(txdata);
      if (tx_packet.bytes.size() == 16 &&
          (tx_packet.bytes[0] === USB_PID_DATA0 || tx_packet.bytes[0] === USB_PID_DATA1)) begin
        tx_data_progress_event.trigger();
      end
    end else if (reset_n && !txvalid && tx_packet_active) begin
      tx_packet_active <= 1'b0;
      tx_packet_count <= tx_packet_count + 1;
      tx_packet_event.trigger(tx_packet);
      if (tx_packet.bytes[0] === USB_PID_DATA0 || tx_packet.bytes[0] === USB_PID_DATA1) begin
        tx_data_packet_event.trigger(tx_packet);
      end
      `uvm_info("USB_UTMI_MON", $sformatf("Observed DUT TX packet %0d with %0d bytes", tx_packet_count + 1, tx_packet.bytes.size()), UVM_HIGH)
      tx_packet = null;
    end
  end
endmodule
