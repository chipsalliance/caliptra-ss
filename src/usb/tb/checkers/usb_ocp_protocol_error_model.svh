// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_protocol_error_model extends uvm_object;
  `uvm_object_utils(usb_ocp_protocol_error_model)
  typedef logic [7:0] bytes_t[$];
  typedef enum {IMAGE_LENGTH, WRITE_CRC, WRITE_RETRY_CRC, READ_STATUS_CRC} error_kind_e;
  // OCP Recovery 1.1 9.2, DEVICE_STATUS protocol-error encodings.
  localparam logic [7:0] LENGTH_ERROR = 8'h03;
  localparam logic [7:0] CRC_ERROR = 8'h04;
  error_kind_e kind;
  logic [6:0] address;
  logic [7:0] setup[8];
  bytes_t payload;
  int unsigned epoch;
  int unsigned generation;
  longint unsigned floor;
  longint unsigned setup_order;
  longint unsigned fault_order;
  int unsigned native_instance;
  int unsigned data_naks;
  int unsigned status_reads;
  int unsigned crc_packets;
  int unsigned clean_retries;
  int unsigned clean_retry_acks;
  int unsigned original_acks;
  longint unsigned original_ack_order;
  longint unsigned bad_token_order;
  longint unsigned silence_end_order;
  longint unsigned clean_ack_order;
  bit sample_setup_debug;
  bit armed;
  bit finished;
  bit setup_seen;
  bit stall_seen;
  bit native_checked;
  bit recovery_seen;
  bit bad_pending;
  bit release_dma;
  bit snapshot_requested;
  bit snapshot_complete;
  logic [31:0] snapshot[string];

  function new(string name = "usb_ocp_protocol_error_model");
    super.new(name);
  endfunction

  function void ocp_configure_request(error_kind_e selected_kind,
      logic [6:0] addr, logic [7:0] iface, logic [7:0] command,
      int unsigned current_epoch, int unsigned next_generation,
      longint unsigned order_floor, bytes_t data, int unsigned read_length = 0);
    if (armed || next_generation == 0 ||
        (selected_kind == READ_STATUS_CRC ?
          (command != OCP_CMD_PROT_CAP || read_length == 0 || read_length > 65535 || data.size() != 0) :
          (data.size() == 0 || read_length != 0 ||
           !(command inside {OCP_CMD_INDIRECT_FIFO_DATA,OCP_CMD_INDIRECT_FIFO_CTRL}) ||
           (selected_kind inside {IMAGE_LENGTH,WRITE_RETRY_CRC} &&
            command != OCP_CMD_INDIRECT_FIFO_DATA))))
      `uvm_fatal("OCP_ERROR_GUARD", "Invalid or duplicate length/CRC experiment")
    kind = selected_kind;
    address = addr;
    epoch = current_epoch;
    generation = next_generation;
    floor = order_floor;
    payload = data;
    setup = '{(kind == READ_STATUS_CRC ? 8'ha1 : 8'h21),OCP_BREQUEST_XFER,
              command,0,iface,0,8'(data.size()+read_length),8'((data.size()+read_length)>>8)};
    armed = 1;
  endfunction

  function bit ocp_check_owner(int device, usb_ocp_base_control c);
    return armed && !finished && device == 1 && c.address === address &&
      c.epoch == epoch && c.generation == generation && c.setup === setup;
  endfunction

  function void ocp_capture_setup(int device, usb_ocp_base_control c);
    if (!armed || finished || device != 1) return;
    if (!setup_seen) begin
      if (!ocp_check_owner(device,c) || c.status_setup_order < floor)
        `uvm_fatal("OCP_ERROR_OWNER", "Accepted SETUP differs from the registered error request")
      setup_seen = 1;
      setup_order = c.status_setup_order;
    end else if (kind == IMAGE_LENGTH && !recovery_seen) begin
      // USB 2.0 8.5.3.4: the next SETUP clears a protocol STALL; no
      // CLEAR_FEATURE is required. It must follow the wire/native STALL.
      if (!stall_seen || !native_checked || c.address !== address ||
          c.epoch != epoch || c.generation != generation+1)
        `uvm_fatal("OCP_ERROR_RECOVERY", "Recovery SETUP preceded the length STALL or its native retirement")
      recovery_seen = 1;
    end
  endfunction

  function void ocp_capture_packet(usb_ocp_event item, usb_ocp_event token,
      int device, usb_ocp_base_control c, usb_ocp_event candidate);
    bit owned_out;
    if (!armed || finished || item.pid == svt_usb_packet::SOF) return;
    if (bad_pending) begin
      // A handshake has no address of its own. Attribute it only to the
      // still-current bad OUT token. A new token ends the response window,
      // but cannot satisfy the separate same-owner clean retry obligation.
      if (item.host_tx && item.pid inside {svt_usb_packet::OUT,svt_usb_packet::PING,
                                         svt_usb_packet::IN,svt_usb_packet::SETUP}) begin
        if (item.address === address && item.endpoint === 0 &&
            !(item.pid inside {svt_usb_packet::OUT,svt_usb_packet::PING}))
          `uvm_fatal("OCP_CRC_RETRY", "Corrupted OUT was replaced instead of retried")
        bad_pending = 0;
        silence_end_order = item.order;
        `uvm_info("OCP_CRC_SILENCE",$sformatf(
          "No DUT response to bad OUT addr=%0d epoch=%0d generation=%0d token=%0d bad=%0d next_token=%0d",
          address,epoch,generation,bad_token_order,fault_order,silence_end_order),UVM_NONE)
      end else if (!item.host_tx && token != null && token.order == bad_token_order &&
                   ocp_check_owner(device,c)) begin
        `uvm_fatal("OCP_CRC_HANDSHAKE", "Corrupted OUT DATA must receive no response (USB 2.0 8.7.2)")
      end else if (item.host_tx && token != null && token.order == bad_token_order &&
                   ocp_check_owner(device,c)) begin
        `uvm_fatal("OCP_CRC_RETRY", "Retry must start with a fresh OUT token")
      end
    end
    if (token == null || !ocp_check_owner(device,c)) return;
    if (kind == IMAGE_LENGTH && !item.host_tx && item.pid == svt_usb_packet::NAK &&
        token.pid inside {svt_usb_packet::OUT,svt_usb_packet::PING})
      data_naks++;
    owned_out = token.pid == svt_usb_packet::OUT &&
      token.address === address && token.endpoint === 0;
    if (kind == IMAGE_LENGTH || !owned_out) return;
    if (item.host_tx && item.packet_valid &&
        item.pid inside {svt_usb_packet::DATA0,svt_usb_packet::DATA1} && crc_packets == 1) begin
      if (item.pid != svt_usb_packet::DATA1 || item.bytes !== payload ||
          !ocp_check_pre_retry_data(c))
        `uvm_fatal("OCP_CRC_RETRY", "Clean retry lost payload/toggle or followed an accepted corrupted packet")
      clean_retries++;
    end
    if (!item.host_tx && item.packet_valid && item.pid inside {svt_usb_packet::ACK,svt_usb_packet::NYET} &&
        candidate != null && candidate.packet_valid && candidate.pid == svt_usb_packet::DATA1 &&
        candidate.bytes === payload) begin
      if (crc_packets == 1) begin
        clean_retry_acks++;
        clean_ack_order = item.order;
      end else if (kind == WRITE_RETRY_CRC) begin
        if (original_acks != 0 || c.data.size() != 0 || !c.active)
          `uvm_fatal("OCP_CRC_LOSS", "A second clean OUT was accepted before retry corruption")
        original_acks++;
        original_ack_order = item.order;
      end
    end
  endfunction

  function bit ocp_check_pre_retry_data(usb_ocp_base_control c);
    if (kind == READ_STATUS_CRC)
      return c.active && !c.status_acked && c.data.size() == OCP_SPEC_LEN_PROT_CAP;
    if (kind == WRITE_RETRY_CRC)
      return c.active && !c.status_acked && c.data === payload &&
        c.next_toggle[0] === 0 && original_acks == 1;
    return c.active && !c.status_acked && c.data.size() == 0;
  endfunction

  function bit ocp_check_invalid_data(int device, usb_ocp_base_control c,
      usb_ocp_event token, usb_ocp_event item);
    if (!ocp_check_owner(device,c) || kind == IMAGE_LENGTH) return 0;
    if (!setup_seen || crc_packets != 0 || token.pid != svt_usb_packet::OUT ||
        token.address !== address || token.endpoint !== 0 || !item.host_tx ||
        item.packet_valid !== 0 || item.packet_crc16_error !== 1 ||
        item.pid != svt_usb_packet::DATA1 ||
        item.bytes !== payload || !ocp_check_pre_retry_data(c))
      `uvm_fatal("OCP_CRC_OWNER", "Invalid DATA does not match the registered corrupt OUT stage")
    crc_packets++;
    fault_order = item.order;
    bad_token_order = token.order;
    bad_pending = 1;
    `uvm_info("OCP_CRC_WIRE", $sformatf(
      "Observed CRC16-bad DATA1 addr=%0d epoch=%0d generation=%0d bytes=%0d order=%0d; no acceptance credit",
      address,epoch,generation,item.bytes.size(),item.order),UVM_NONE)
    return 1;
  endfunction

  function bit ocp_check_stall(int device, usb_ocp_base_control c,
      usb_ocp_event token, usb_ocp_event item, usb_ocp_event candidate);
    if (!ocp_check_owner(device,c)) return 0;
    if (kind != IMAGE_LENGTH || !setup_seen || stall_seen || !c.active ||
        c.status_acked || c.data.size() != 0 || item.host_tx || !item.packet_valid ||
        token.endpoint !== 0 || token.address !== address ||
        !(token.pid inside {svt_usb_packet::OUT,svt_usb_packet::PING}) ||
        (token.pid == svt_usb_packet::OUT &&
         (candidate == null || !candidate.packet_valid || !candidate.host_tx ||
          candidate.bytes !== payload)) || token.order <= setup_order)
      `uvm_fatal("OCP_ERROR_STAGE", "Expected length error must STALL DATA before accepting any bytes")
    stall_seen = 1;
    fault_order = item.order;
    return 1;
  endfunction

  function bit ocp_check_terminal_transfer(usb_ocp_event item);
    logic [`SVT_USB_RESULTS_STATUS_SIZE-1:0] allowed;
    if (!armed || finished || item.address !== address || item.setup !== setup ||
        kind != IMAGE_LENGTH) return 0;
    allowed = 0;
    allowed[4] = 1;
    allowed[5] = 1;
    if (!stall_seen || native_checked || item.endpoint !== 0 ||
        item.transfer_type != svt_usb_transfer::CONTROL_TRANSFER ||
        item.transfer_start_order < floor || item.transfer_start_order >= setup_order ||
        item.order <= fault_order || !item.native_aborted || item.transfer_ok !== 0 ||
        item.results[4] !== 1 || (item.results & ~allowed) !== 0 ||
        item.bytes.size() > payload.size())
      `uvm_fatal("OCP_ERROR_NATIVE", "Length rejection lacks exact wire/native STALL retirement")
    native_checked = 1;
    native_instance = item.vendor_instance;
    return 1;
  endfunction

  function void ocp_capture_crosscheck(int device, usb_ocp_base_control c,
      usb_ocp_event item);
    if (ocp_check_owner(device,c) && kind != IMAGE_LENGTH) begin
      // The device may legally NAK a clean retry, so require at least one.
      if (native_checked || crc_packets != 1 || clean_retries == 0 ||
          clean_retry_acks != 1 || bad_pending || silence_end_order <= fault_order ||
          clean_ack_order <= silence_end_order || clean_ack_order > c.status_complete_order ||
          item.transfer_start_order < floor || item.transfer_start_order >= setup_order ||
          (kind != WRITE_CRC && !item.expected_device_timeout) ||
          (kind == WRITE_RETRY_CRC && (original_acks != 1 || original_ack_order >= bad_token_order)) ||
          (kind != READ_STATUS_CRC && c.data !== payload) ||
          (kind == READ_STATUS_CRC && c.status_complete_order != clean_ack_order) ||
          !c.status_acked)
        `uvm_fatal("OCP_CRC_NATIVE", "Corrupt OUT lacks a clean same-native retry and exact completion")
      native_checked = 1;
      native_instance = item.vendor_instance;
      `uvm_info("OCP_CRC_RETRY",$sformatf(
        "kind=%s native=%0d first_ack=%0d bad=%0d clean_ack=%0d status_ack=%0d",
        kind.name(),native_instance,original_ack_order,fault_order,
        clean_ack_order,c.status_complete_order),UVM_NONE)
    end
  endfunction

  function bit ocp_check_status_owned(usb_ocp_base_control c);
    return armed && !finished && native_checked && c.address === address &&
      c.epoch == epoch && c.generation > generation &&
      (!(kind inside {WRITE_RETRY_CRC,READ_STATUS_CRC}) ||
       (c.generation == generation+status_reads+1 && c.setup[0] === 8'ha1 &&
        c.setup[1] === OCP_BREQUEST_XFER && c.ocp_get_value() === 16'(OCP_CMD_DEVICE_STATUS) &&
        c.ocp_get_index() === {8'b0,setup[4]}));
  endfunction

  function void ocp_check_status(usb_ocp_base_control c);
    logic [7:0] expected;
    if (!ocp_check_status_owned(c) || status_reads >= 2 ||
        (kind == IMAGE_LENGTH && (!stall_seen || !recovery_seen)))
      `uvm_fatal("OCP_ERROR_RTC_ORDER", "Error read-clear is outside its registered recovery window")
    expected = (status_reads == 0 && kind != READ_STATUS_CRC) ?
      ((kind == IMAGE_LENGTH) ? LENGTH_ERROR : CRC_ERROR) : OCP_PROTOCOL_ERROR_NONE;
    if (c.data[1] !== expected)
      `uvm_error("OCP_ERROR_STATUS", $sformatf(
        "read=%0d code=%02h expected=%02h kind=%s",
        status_reads+1,c.data[1],expected,kind.name()))
    status_reads++;
    if (kind != IMAGE_LENGTH && c.data[1] === expected)
      `uvm_info("OCP_CRC_STATUS",$sformatf(
        "kind=%s read=%0d generation=%0d code=%02h expected=%02h",
        kind.name(),status_reads,c.generation,c.data[1],expected),UVM_NONE)
  endfunction

  function void ocp_capture_control(int device, usb_ocp_base_control c);
    if (!armed || finished || device != 1) return;
    if (kind == IMAGE_LENGTH && c.generation == generation)
      `uvm_fatal("OCP_LENGTH_ACCEPTED", "Image-remainder overflow incorrectly completed STATUS")
  endfunction

  function void ocp_check_complete();
    if (!armed || !finished || !setup_seen || !native_checked || status_reads != 2 ||
        (kind == IMAGE_LENGTH && (!stall_seen || !recovery_seen)) ||
        (kind != IMAGE_LENGTH && (crc_packets != 1 || clean_retries == 0 || clean_retry_acks != 1)))
      `uvm_fatal("OCP_ERROR_INCOMPLETE", "Error/retry/native/recovery/read-clear obligations remain unreached")
  endfunction
endclass
