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

// Owned snapshots only: no retained vendor transaction or payload handles.
class usb_ocp_event extends uvm_sequence_item;
  `uvm_object_utils(usb_ocp_event)
  // svt_usb_transfer::results_status: native CMD abort/flush, not generic abort().
  localparam int unsigned SERVICE_ABORT_RESULT_BIT = 1;

  typedef enum {USB_PACKET, USB_TRANSFER, AXI_COMPLETED} kind_e;
  kind_e kind;
  longint unsigned order;
  realtime observed_at;
  logic host_tx;
  svt_usb_packet::pid_name_enum pid;
  logic packet_valid;
  logic [6:0] address;
  logic [3:0] endpoint;
  logic [7:0] bytes[$];
  logic [7:0] setup[8];
  logic transfer_ok;
  bit native_aborted;
  logic [`SVT_USB_RESULTS_STATUS_SIZE-1:0] results;
  // AXI events retain the completed callback object's native instance here.
  int unsigned vendor_instance;
  longint unsigned transfer_start_order;
  longint unsigned transfer_serial;
  int unsigned manager;
  logic write_access;
  logic [63:0] axi_address;
  int unsigned axi_id;
  // Accepted AXI object identity can differ from its completion callback.
  int unsigned axi_instance;
  int unsigned axi_beats;
  int unsigned axi_beat_bytes;
  logic [1:0] axi_burst;
  logic [1:0] axi_responses[$];
  logic [7:0] strobes[$];
  logic response_ok;
  svt_usb_transfer::transfer_type_enum transfer_type;
  int unsigned completed_bytes;
  longint unsigned sof_serial;
  logic [10:0] frame_number;
  // USB device/epoch/SETUP generation lives in usb_ocp_base_control.
  // DATA and handshakes never establish context from their address fields.

  function new(string name = "usb_ocp_event");
    super.new(name);
  endfunction
endclass
