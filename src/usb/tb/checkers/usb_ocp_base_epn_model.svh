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

// Passive EPN acceptance ledger. Native packet actuals are authoritative;
// monitor transfer payloads and completed firmware SRAM reads cross-check them.
class usb_ocp_base_epn_model extends uvm_object;
  `uvm_object_utils(usb_ocp_base_epn_model)
  typedef logic [7:0] bytes_t[$];
  usb_ocp_base_epn_descriptor discovery;
  usb_ocp_event token;
  usb_ocp_event candidate;
  int unsigned device = 1;
  int unsigned data_tag;
  logic [6:0] address;
  // Learned from device0 SET_ADDRESS, never the peer's descriptor EP0.
  logic [6:0] control_address;
  bit configured;
  bit enabled;
  logic [7:0] active_alternate;
  int unsigned accepted[2];
  int unsigned crosschecked[2];
  int unsigned memory_checked[2];
  logic next_toggle[2];
  bytes_t previous[2];
  longint unsigned accepted_token[2][2];
  longint unsigned accepted_data[2][2];
  longint unsigned accepted_order[2][2];
  longint unsigned accepted_sof[2][2];
  int unsigned accepted_generation[2][2];
  int unsigned token_generation;
  int unsigned token_phase;
  int unsigned token_direction;
  logic [63:0] memory_base;
  logic [31:0] list_base;
  logic armed[2];
  logic retired[2];
  int unsigned read_offset;
  bit negative_payload;
  bit iso_no_handshake;
  longint unsigned last_iso_token[2];
  bit iso_token_seen[2];
  longint unsigned interrupt_next_poll[2];
  bit interrupt_nak_seen[2];
  bit sof_seen;
  bit frame_edge_seen;
  logic [10:0] last_frame;
  int unsigned same_frame_sofs;
  realtime last_sof_at;
  longint unsigned last_sof_serial;

  function new(string name = "usb_ocp_base_epn_model");
    super.new(name);
    discovery = usb_ocp_base_epn_descriptor::type_id::create("discovery");
    accepted = '{default:0};
    crosschecked = '{default:0};
    memory_checked = '{default:0};
    next_toggle = '{default:0};
    armed = '{default:0};
    retired = '{default:0};
    iso_token_seen = '{default:0};
    interrupt_nak_seen = '{default:0};
  endfunction

  function svt_usb_transfer::transfer_type_enum ocp_get_transfer_type(int dir);
    case (discovery.endpoints[dir].transfer_type)
      USB_TRANSFER_TYPE_BULK: return dir ? svt_usb_transfer::BULK_IN_TRANSFER :
                                        svt_usb_transfer::BULK_OUT_TRANSFER;
      USB_TRANSFER_TYPE_INTERRUPT: return dir ? svt_usb_transfer::INTERRUPT_IN_TRANSFER :
                                             svt_usb_transfer::INTERRUPT_OUT_TRANSFER;
      USB_TRANSFER_TYPE_ISOCHRONOUS: return dir ? svt_usb_transfer::ISOCHRONOUS_IN_TRANSFER :
                                               svt_usb_transfer::ISOCHRONOUS_OUT_TRANSFER;
      default: `uvm_fatal("OCP_EPN_TYPE", "No discovered noncontrol type")
    endcase
  endfunction

  function void ocp_check_window(usb_ocp_base_control c);
    if (!c.active || c.status_acked || c.generation != token_generation ||
        (device == 2 && c.address !== control_address) ||
        c.setup[0] !== ((token_phase == 0) ? 8'ha1 : 8'h21) ||
        c.ocp_get_value() !== ((token_phase == 0) ?
          16'(OCP_CMD_PROT_CAP) : 16'(OCP_CMD_INDIRECT_FIFO_DATA)))
      `uvm_fatal("OCP_EPN_OVERLAP", "EPN transaction is outside its matching active OCP window")
  endfunction

  // USB 2.0 8.4.3: native wire SOFs, not shared_status, establish service
  // opportunities. At HS eight consecutive microframes carry one frame value.
  function void ocp_check_sof(usb_ocp_event item);
    logic [10:0] next_frame;
    realtime gap;
    if (!item.host_tx || item.packet_valid !== 1 || $isunknown(item.frame_number))
      `uvm_fatal("OCP_EPN_SOF", "Invalid native SOF snapshot")
    if (sof_seen) begin
      gap = item.observed_at-last_sof_at;
      // Packet-end timestamps include bit-stuff/PHY quantization jitter.
      // A 1 us envelope checks the 125 us cadence without fabricating exact
      // physical edges; parent waveform validation measures actual timing.
      if (gap < 124us || gap > 126us || item.sof_serial != last_sof_serial+1)
        `uvm_fatal("OCP_EPN_SOF", "Native HS SOF cadence/ordinal is not 125 us")
      next_frame = last_frame + 11'd1;
      if (item.frame_number === last_frame) begin
        same_frame_sofs++;
        if (same_frame_sofs > 8)
          `uvm_fatal("OCP_EPN_SOF", "More than eight HS SOFs in a frame")
      end else if (item.frame_number === next_frame) begin
        if (frame_edge_seen && same_frame_sofs != 8)
          `uvm_fatal("OCP_EPN_SOF", "Frame advanced without eight HS microframes")
        frame_edge_seen = 1;
        same_frame_sofs = 1;
      end else `uvm_fatal("OCP_EPN_SOF", "Native frame bits skipped or regressed")
    end else same_frame_sofs = 1;
    last_frame = item.frame_number;
    last_sof_at = item.observed_at;
    last_sof_serial = item.sof_serial;
    sof_seen = 1;
  endfunction

  function void ocp_check_accept(usb_ocp_event data, usb_ocp_base_control c);
    bytes_t expected;
    logic [7:0] expected_byte;
    usb_endpoint_cfg ep;
    int dir;
    int phase;
    dir = token_direction;
    phase = accepted[dir];
    ep = discovery.endpoints[dir];
    ocp_check_window(c);
    if (phase > 1 || phase != token_phase)
      `uvm_fatal("OCP_EPN_STREAM", "Extra, duplicate, or wrong-phase accepted stream")
    expected = usb_ocp_base_epn_profile::ocp_prepare_stream(
      dir ? USB_DIRECTION_IN : USB_DIRECTION_OUT,phase,data_tag);
    if (data.bytes.size() != expected.size() || data.bytes.size() > ep.max_packet_size)
      `uvm_fatal("OCP_EPN_STREAM", "Accepted EPN packet length differs from planned stream")
    foreach (expected[i]) begin
      expected_byte = expected[i];
      // Only a private expected byte changes. Actuals/ledgers remain intact.
      if (negative_payload && phase == 1 && dir == 0 && i == 0) expected_byte ^= 1;
      if (data.bytes[i] !== expected_byte)
        `uvm_fatal("OCP_EPN_PAYLOAD",$sformatf(
          "slot=%0d ep=%0d dir=%0d phase=%0d byte=%0d actual=%02h expected=%02h negative=%0b",
          device,ep.ep_number,dir,phase,i,data.bytes[i],expected_byte,negative_payload))
    end
    // USB 2.0 5.6.4/5.7.4: at most one accepted opportunity per interval
    // for this non-high-bandwidth pair. NAK retries do not advance service.
    if (ep.transfer_type != USB_TRANSFER_TYPE_BULK &&
        (!sof_seen || token.sof_serial == 0 ||
         token.sof_serial != last_sof_serial || data.sof_serial != token.sof_serial ||
         token.observed_at < last_sof_at || data.observed_at-last_sof_at >= 125us ||
         (phase != 0 &&
         token.sof_serial < accepted_sof[dir][phase-1] + (1 << (ep.interval-1)))))
      `uvm_fatal("OCP_EPN_INTERVAL", "Periodic service violates discovered bInterval")
    accepted_token[dir][phase] = token.order;
    accepted_data[dir][phase] = data.order;
    accepted_order[dir][phase] = data.order;
    // The acceptance order itself is assigned by the caller below for ACK.
    accepted_sof[dir][phase] = token.sof_serial;
    accepted_generation[dir][phase] = c.generation;
    previous[dir] = data.bytes;
    accepted[dir]++;
  endfunction

  function void ocp_observe_packet(usb_ocp_event item, usb_ocp_base_control c);
    usb_endpoint_cfg ep;
    bit incoming;
    bit iso;
    bit toggle;
    int phase;
    if (item.host_tx && item.pid inside {svt_usb_packet::IN,
        svt_usb_packet::OUT,svt_usb_packet::PING}) begin
      if (token != null && candidate != null)
        `uvm_fatal("OCP_EPN_PACKET", "New token abandoned unaccepted EPN DATA")
      token = item;
      candidate = null;
      token_direction = (item.pid == svt_usb_packet::IN);
      ep = discovery.endpoints[token_direction];
      if (!enabled || ep == null || item.packet_valid !== 1 ||
          item.address !== address || item.endpoint !== 4'(ep.ep_number))
        `uvm_fatal("OCP_EPN_IDENTITY", "EPN token is not a configured discovered endpoint")
      token_generation = c.generation;
      if (c.setup[0] === 8'ha1 && c.ocp_get_value() === 16'(OCP_CMD_PROT_CAP))
        token_phase = 0;
      else if (c.setup[0] === 8'h21 &&
               c.ocp_get_value() === 16'(OCP_CMD_INDIRECT_FIFO_DATA)) token_phase = 1;
      else `uvm_fatal("OCP_EPN_OVERLAP", "EPN token outside selected OCP read/write")
      ocp_check_window(c);
      iso_no_handshake = 0;
      if (ep.transfer_type == USB_TRANSFER_TYPE_ISOCHRONOUS) begin
        if (iso_token_seen[token_direction] &&
            item.sof_serial < last_iso_token[token_direction] + (1 << (ep.interval-1)))
          `uvm_fatal("OCP_EPN_ISO", "ISO retry/multiple tokens in one service opportunity")
        iso_token_seen[token_direction] = 1;
        last_iso_token[token_direction] = item.sof_serial;
      end
      if (ep.transfer_type == USB_TRANSFER_TYPE_INTERRUPT) begin
        // USB 2.0 5.7.4: this host selected the descriptor's polling period.
        // NAK postpones polling, unlike a retry of a transmission error.
        if (interrupt_nak_seen[token_direction] &&
            item.sof_serial < interrupt_next_poll[token_direction])
          `uvm_fatal("OCP_EPN_INTERVAL", "Interrupt re-poll before the next NAK service opportunity")
        interrupt_nak_seen[token_direction] = 0;
      end
      if (item.pid == svt_usb_packet::PING &&
          ep.transfer_type != USB_TRANSFER_TYPE_BULK)
        `uvm_fatal("OCP_EPN_PACKET", "Only HS BULK in this pair may use PING")
      return;
    end
    if (token == null) `uvm_fatal("OCP_EPN_PACKET", "EPN response without token")
    incoming = token_direction;
    ep = discovery.endpoints[token_direction];
    iso = (ep.transfer_type == USB_TRANSFER_TYPE_ISOCHRONOUS);
    if (item.pid inside {svt_usb_packet::DATA0,svt_usb_packet::DATA1}) begin
      if (item.host_tx === incoming || item.packet_valid !== 1 ||
          token.pid == svt_usb_packet::PING || candidate != null)
        `uvm_fatal("OCP_EPN_PACKET", "Invalid EPN DATA direction/CRC/context")
      if (iso) begin
        // USB 2.0 5.6.5/8.5.5: single HS ISO DATA0, no handshake.
        if (item.pid !== svt_usb_packet::DATA0)
          `uvm_fatal("OCP_EPN_ISO", "Single-transaction HS ISO requires DATA0")
        ocp_check_accept(item,c);
        iso_no_handshake = 1;
        token = null;
      end else candidate = item;
      return;
    end
    if (iso) `uvm_fatal("OCP_EPN_ISO", "ISO handshake/retry is forbidden")
    if (item.pid == svt_usb_packet::NAK) begin
      if (item.host_tx !== 0 || (incoming && candidate != null))
        `uvm_fatal("OCP_EPN_PACKET", "Invalid NAK responder/context")
      if (ep.transfer_type == USB_TRANSFER_TYPE_INTERRUPT) begin
        interrupt_next_poll[token_direction] =
          token.sof_serial + (1 << (ep.interval-1));
        interrupt_nak_seen[token_direction] = 1;
      end
      candidate = null;
      token = null;
      return;
    end
    if (item.pid == svt_usb_packet::STALL)
      `uvm_fatal("OCP_EPN_STALL", "Unexpected noncontrol endpoint halt")
    if (!(item.pid inside {svt_usb_packet::ACK,svt_usb_packet::NYET}) ||
        item.host_tx !== incoming || (incoming && item.pid != svt_usb_packet::ACK) ||
        (item.pid == svt_usb_packet::NYET && ep.transfer_type != USB_TRANSFER_TYPE_BULK))
      `uvm_fatal("OCP_EPN_PACKET", "Invalid accepting handshake")
    if (token.pid == svt_usb_packet::PING) begin
      if (candidate != null || item.pid != svt_usb_packet::ACK)
        `uvm_fatal("OCP_EPN_PACKET", "PING cannot accept payload")
    end else begin
      if (candidate == null) `uvm_fatal("OCP_EPN_PACKET", "Handshake without EPN DATA")
      toggle = (candidate.pid == svt_usb_packet::DATA1);
      if (toggle === next_toggle[token_direction]) begin
        phase = accepted[token_direction];
        ocp_check_accept(candidate,c);
        accepted_order[token_direction][phase] = item.order;
        next_toggle[token_direction] = !toggle;
      end else begin
        if (accepted[token_direction] == 0 || candidate.bytes !== previous[token_direction])
          `uvm_fatal("OCP_EPN_TOGGLE", "Retry does not reproduce the previous accepted packet")
      end
    end
    token = null;
    candidate = null;
  endfunction

  function void ocp_check_transfer(usb_ocp_event item);
    int dir;
    int phase;
    bytes_t expected;
    dir = -1;
    foreach (discovery.endpoints[i])
      if (discovery.endpoints[i] != null &&
          item.endpoint === 4'(discovery.endpoints[i].ep_number) &&
          item.transfer_type === ocp_get_transfer_type(i)) dir = i;
    if (dir < 0 || item.address !== address)
      `uvm_fatal("OCP_EPN_CORRELATION", "Monitor EPN identity differs from discovery")
    phase = crosschecked[dir];
    if (phase > 1 || accepted[dir] <= phase || !item.transfer_ok ||
        item.results !== 0 || item.transfer_start_order > accepted_token[dir][phase] ||
        item.order < accepted_order[dir][phase])
      `uvm_fatal("OCP_EPN_CORRELATION", "Unsuccessful/unmatched actual EPN transfer")
    expected = usb_ocp_base_epn_profile::ocp_prepare_stream(
      dir ? USB_DIRECTION_IN : USB_DIRECTION_OUT,phase,data_tag);
    if (item.completed_bytes !== expected.size() || item.bytes !== expected)
      `uvm_fatal("OCP_EPN_CORRELATION", "Monitor bytes differ from accepted independent stream")
    crosschecked[dir]++;
  endfunction

  function void ocp_check_axi(usb_ocp_event item);
    usb_ep_entry_t entry;
    bytes_t expected;
    logic [63:0] offset;
    int phase;
    if (item.manager != ((device == 1) ? 1 : 3)) return;
    offset = item.axi_address - memory_base;
    foreach (discovery.endpoints[dir]) begin
      if (discovery.endpoints[dir] == null) continue;
      phase = memory_checked[dir];
      if (offset == list_base + discovery.endpoints[dir].entry_offset() &&
          item.bytes.size() == 4) begin
        entry = {item.bytes[3],item.bytes[2],item.bytes[1],item.bytes[0]};
        if (item.write_access && entry.active === 1) begin
          if (phase > 1 || armed[dir])
            `uvm_fatal("OCP_EPN_SRAM", "Rearm before prior SRAM proof or extra packet")
          armed[dir] = 1;
        end
        if (!item.write_access && armed[dir] && entry.active === 0) begin
          if (phase > 1 || accepted[dir] <= phase || entry.nbytes !== 0 ||
              entry.stall !== 0 || entry.disabled !== 0 ||
              entry.buffer_offset !==
                usb_ocp_base_epn_profile::ocp_get_retired_buffer_offset(
                  dir ? USB_DIRECTION_IN : USB_DIRECTION_OUT,phase))
            `uvm_fatal("OCP_EPN_SRAM", "Retirement lacks accepted bytes or exact writeback")
          retired[dir] = 1;
          if (dir == 1) begin
            memory_checked[dir]++;
            armed[dir] = 0;
            retired[dir] = 0;
          end
        end
      end
    end
    phase = memory_checked[0];
    if (!item.write_access && retired[0] && phase < 2 &&
        offset >= usb_ocp_base_epn_profile::ocp_get_buffer(USB_DIRECTION_OUT) &&
        offset < usb_ocp_base_epn_profile::ocp_get_buffer(USB_DIRECTION_OUT)+64) begin
      expected = usb_ocp_base_epn_profile::ocp_prepare_stream(USB_DIRECTION_OUT,phase,data_tag);
      if (offset != usb_ocp_base_epn_profile::ocp_get_buffer(USB_DIRECTION_OUT)+read_offset ||
          item.bytes.size() != 4 || item.response_ok !== 1)
        `uvm_fatal("OCP_EPN_SRAM", "OUT SRAM proof is unordered or unsuccessful")
      foreach (item.bytes[i])
        if (read_offset+i < expected.size() && item.bytes[i] !== expected[read_offset+i])
          `uvm_fatal("OCP_EPN_SRAM", "OUT SRAM accepted bytes differ from independent stream")
      read_offset += 4;
      if (read_offset >= expected.size()) begin
        memory_checked[0]++;
        armed[0] = 0;
        retired[0] = 0;
        read_offset = 0;
      end
    end
  endfunction

  function bit ocp_check_drained();
    return token == null && candidate == null &&
      accepted[0] == 2 && accepted[1] == 2 &&
      crosschecked[0] == 2 && crosschecked[1] == 2 &&
      memory_checked[0] == 2 && memory_checked[1] == 2 &&
      !armed[0] && !armed[1] && !retired[0] && !retired[1] &&
      !interrupt_nak_seen[0] && !interrupt_nak_seen[1];
  endfunction
endclass
