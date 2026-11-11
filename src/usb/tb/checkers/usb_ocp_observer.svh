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

class usb_ocp_observer extends uvm_component;
  `uvm_component_utils(usb_ocp_observer)

  protected usb_ocp_event pending[$];
  protected usb_ocp_event completions[$];
  protected longint unsigned completion_version;
  protected longint unsigned started_at[int unsigned];
  protected longint unsigned started_serial[int unsigned];
  longint unsigned transfer_starts;
  longint unsigned next_order;
  int unsigned packet_count;
  int unsigned transfer_count;
  int unsigned reordered_completions;
  int unsigned axi_count[4];
  int unsigned outstanding_axi[4];
  longint unsigned sof_serial;
  usb_ocp_base_service_callback service_callback;
  usb_ocp_suspend_link_callback l2_link_callback;
  localparam int unsigned QUEUE_LIMIT = 16384;

  function new(string name = "usb_ocp_observer", uvm_component parent = null);
    super.new(name, parent);
    next_order = 0;
    packet_count = 0;
    transfer_count = 0;
    reordered_completions = 0;
    transfer_starts = 0;
    completion_version = 0;
    axi_count = '{default:0};
    outstanding_axi = '{default:0};
  endfunction

  // The documented svt_usb_types enums describe field values, not packed
  // widths. USB 2.0 Table 9-2 specifies the wire's 1/2/5-bit layout.
  function logic [7:0] ocp_prepare_request_type(
      svt_usb_types::setup_data_bmrequesttype_dir_enum direction,
      svt_usb_types::setup_data_bmrequesttype_type_enum request_type,
      svt_usb_types::setup_data_bmrequesttype_recipient_enum recipient);
    logic [7:0] packed_type;
    packed_type = 0;
    case (direction)
      svt_usb_types::HOST_TO_DEVICE: packed_type[7] = 1'b0;
      svt_usb_types::DEVICE_TO_HOST: packed_type[7] = 1'b1;
      default: `uvm_fatal("OCP_SETUP_ENCODING", "Unknown/unsupported SETUP direction enum")
    endcase
    case (request_type)
      svt_usb_types::STANDARD: packed_type[6:5] = 2'b00;
      svt_usb_types::CLASS: packed_type[6:5] = 2'b01;
      svt_usb_types::VENDOR: packed_type[6:5] = 2'b10;
      default: `uvm_fatal("OCP_SETUP_ENCODING", "Unknown/reserved SETUP type enum")
    endcase
    case (recipient)
      svt_usb_types::BMREQ_DEVICE: packed_type[4:0] = 5'd0;
      svt_usb_types::BMREQ_INTERFACE: packed_type[4:0] = 5'd1;
      svt_usb_types::BMREQ_ENDPOINT: packed_type[4:0] = 5'd2;
      svt_usb_types::BMREQ_OTHER: packed_type[4:0] = 5'd3;
      default: `uvm_fatal("OCP_SETUP_ENCODING", "Unknown/reserved USB2 SETUP recipient enum")
    endcase
    return packed_type;
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Host randomization constrains the same enums to wire field values.
    // Guard their numeric encodings without assuming enum storage widths.
    if (svt_usb_types::HOST_TO_DEVICE !== 0 || svt_usb_types::DEVICE_TO_HOST !== 1 ||
        svt_usb_types::STANDARD !== 0 || svt_usb_types::CLASS !== 1 ||
        svt_usb_types::VENDOR !== 2 || svt_usb_types::BMREQ_DEVICE !== 0 ||
        svt_usb_types::BMREQ_INTERFACE !== 1 || svt_usb_types::BMREQ_ENDPOINT !== 2 ||
        svt_usb_types::BMREQ_OTHER !== 3)
      `uvm_fatal("OCP_SETUP_ENCODING", "Installed VIP enum values differ from host wire-field constraints")
    if (ocp_prepare_request_type(svt_usb_types::DEVICE_TO_HOST,svt_usb_types::STANDARD,
                                svt_usb_types::BMREQ_DEVICE) !== 8'h80 ||
        ocp_prepare_request_type(svt_usb_types::HOST_TO_DEVICE,svt_usb_types::CLASS,
                                svt_usb_types::BMREQ_OTHER) !== 8'h23 ||
        ocp_prepare_request_type(svt_usb_types::DEVICE_TO_HOST,svt_usb_types::CLASS,
                                svt_usb_types::BMREQ_INTERFACE) !== 8'ha1)
      `uvm_fatal("OCP_SETUP_ENCODING", "SETUP 1/2/5-bit encoding self-check failed")
  endfunction

  function void ocp_publish_snapshot(usb_ocp_event item);
    if (item == null || pending.size() >= QUEUE_LIMIT) begin
      `uvm_fatal("OCP_OBSERVER", "Null snapshot or bounded observation queue overflow")
    end
    item.order = next_order++;
    item.observed_at = $realtime;
    pending.push_back(item);
  endfunction

  function void ocp_capture_packet(svt_usb_packet pkt, logic host_tx);
    usb_ocp_event item;
    if (pkt == null) `uvm_fatal("OCP_OBSERVER", "Null packet callback")
    item = usb_ocp_event::type_id::create("packet_snapshot");
    item.kind = usb_ocp_event::USB_PACKET;
    item.host_tx = host_tx;
    item.pid = pkt.pid_name;
    // CRC errors must not establish packet acceptance (USB 2.0 8.7).
    item.packet_valid = !pkt.crc_error_detected();
    item.address = pkt.device_address;
    item.endpoint = pkt.ept_num;
    if (item.pid === svt_usb_packet::SOF)
      item.frame_number = pkt.get_frame_number_val();
    // A wire SOF ordinal, independent of submitted periodic scheduling.
    if (host_tx && item.pid === svt_usb_packet::SOF && item.packet_valid)
      sof_serial++;
    item.sof_serial = sof_serial;
    if (pkt.get_payload_byte_count() != 0 &&
        (pkt.payload == null || pkt.payload_offset < 0 ||
         pkt.payload_offset + pkt.get_payload_byte_count() > pkt.payload.data.size()))
      `uvm_fatal("OCP_OBSERVER", "Packet payload window exceeds owned data")
    for (int i = 0; i < pkt.get_payload_byte_count(); i++) begin
      if (pkt.payload == null) `uvm_fatal("OCP_OBSERVER", "Packet payload missing")
      item.bytes.push_back(pkt.payload.get_byte_val(pkt.payload_offset + i));
    end
    packet_count++;
    ocp_publish_snapshot(item);
  endfunction

  function void ocp_capture_transfer_start(svt_usb_transfer xfer);
    int unsigned identity;
    if (xfer == null) `uvm_fatal("OCP_OBSERVER", "Null transfer-start callback")
    if (!(xfer.xfer_type inside {svt_usb_transfer::CONTROL_TRANSFER,
        svt_usb_transfer::BULK_IN_TRANSFER,svt_usb_transfer::BULK_OUT_TRANSFER,
        svt_usb_transfer::INTERRUPT_IN_TRANSFER,svt_usb_transfer::INTERRUPT_OUT_TRANSFER,
        svt_usb_transfer::ISOCHRONOUS_IN_TRANSFER,svt_usb_transfer::ISOCHRONOUS_OUT_TRANSFER}))
      `uvm_fatal("OCP_OBSERVER", "Unsupported transfer type in OCP-only environment")
    identity = xfer.get_inst_id();
    if (started_at.exists(identity))
      `uvm_fatal("OCP_CORRELATION", "Transfer instance started twice without completion")
    started_at[identity] = next_order++;
    started_serial[identity] = transfer_starts++;
  endfunction

  function void ocp_capture_transfer(svt_usb_transfer xfer);
    usb_ocp_event item;
    if (xfer == null) `uvm_fatal("OCP_OBSERVER", "Null transfer callback")
    item = usb_ocp_event::type_id::create("transfer_snapshot");
    item.kind = usb_ocp_event::USB_TRANSFER;
    item.address = xfer.device_address;
    item.endpoint = xfer.endpoint_number;
    item.transfer_type = xfer.xfer_type;
    if (xfer.xfer_type != svt_usb_transfer::CONTROL_TRANSFER)
      item.completed_bytes = xfer.completed_payload_bytes();
    item.vendor_instance = xfer.get_inst_id();
    if (!started_at.exists(item.vendor_instance))
      `uvm_fatal("OCP_CORRELATION", "Ended transfer instance has no matching monitor start")
    item.transfer_start_order = started_at[item.vendor_instance];
    item.transfer_serial = started_serial[item.vendor_instance];
    started_at.delete(item.vendor_instance);
    started_serial.delete(item.vendor_instance);
    item.transfer_ok = (xfer.status === svt_sequence_item::ACCEPT);
    item.results = xfer.results_status;
    if (xfer.xfer_type == svt_usb_transfer::CONTROL_TRANSFER) begin
      item.setup[0] = ocp_prepare_request_type(xfer.setup_data_bmrequesttype_dir,
                                              xfer.setup_data_bmrequesttype_type,
                                              xfer.setup_data_bmrequesttype_recipient);
      item.setup[1] = xfer.setup_data_brequest;
      item.setup[2] = xfer.setup_data_w_value[7:0];
      item.setup[3] = xfer.setup_data_w_value[15:8];
      item.setup[4] = xfer.setup_data_w_index[7:0];
      item.setup[5] = xfer.setup_data_w_index[15:8];
      item.setup[6] = xfer.setup_data_w_length[7:0];
      item.setup[7] = xfer.setup_data_w_length[15:8];
    end
    if (xfer.payload != null) begin
      if (xfer.payload_start_ix < 0 ||
          xfer.payload_start_ix + xfer.payload_byte_count() > xfer.payload.data.size())
        `uvm_fatal("OCP_OBSERVER", "Transfer payload window exceeds owned data")
      for (int i = 0; i < xfer.payload_byte_count(); i++)
        item.bytes.push_back(xfer.payload.get_byte_val(xfer.payload_start_ix+i));
    end
    if (completions.size() >= QUEUE_LIMIT)
      `uvm_fatal("OCP_OBSERVER", "Unconsumed control completion queue overflow")
    transfer_count++;
    ocp_publish_snapshot(item);
    completions.push_back(item);
    completion_version++;
  endfunction

  // Callback tasks call this only after Avery read_done/write_done. No
  // submitted-intent observation and no DUT hierarchy reads are used.
  function void ocp_capture_axi(aaxi_master_tr tr, int unsigned manager);
    usb_ocp_event item;
    if (tr == null || manager >= 4)
      `uvm_fatal("OCP_OBSERVER", "Invalid Avery completed transaction")
    item = usb_ocp_event::type_id::create("axi_snapshot");
    item.kind = usb_ocp_event::AXI_COMPLETED;
    item.manager = manager;
    item.axi_address = tr.addr;
    item.axi_id = tr.id;
    item.axi_instance = tr.get_inst_id();
    item.axi_beats = int'(tr.len) + 1;
    item.axi_beat_bytes = 1 << tr.size;
    item.axi_burst = tr.burst;
    item.write_access = (tr.kind == AAXI_WRITE);
    item.response_ok = 1'b1;
    if (tr.size != 2 || item.axi_beats > 16 ||
        (tr.len != 0 && (item.write_access || item.axi_burst !== AAXI_BURST_FIXED)))
      `uvm_fatal("OCP_OBSERVER", "Recovery accesses require DWORDs and at most 16 FIXED read beats")
    if (item.write_access) begin
      item.response_ok = (tr.resp === AAXI_RESP_OKAY);
      item.axi_responses.push_back(tr.resp);
      foreach (tr.strobes[i]) item.strobes.push_back({7'b0, tr.strobes[i]});
    end else begin
      item.response_ok = (tr.rresp_Q.size() == item.axi_beats);
      foreach (tr.rresp_Q[i]) begin
        item.axi_responses.push_back(tr.rresp_Q[i]);
        item.response_ok &= (tr.rresp_Q[i] === AAXI_RESP_OKAY);
      end
    end
    foreach (tr.data[i]) item.bytes.push_back(tr.data[i]);
    if (item.bytes.size() != item.axi_beats*item.axi_beat_bytes)
      `uvm_fatal("OCP_OBSERVER", "Avery completed transaction has wrong byte count")
    axi_count[manager]++;
    ocp_publish_snapshot(item);
  endfunction

  task ocp_wait_snapshot(output usb_ocp_event item);
    wait (pending.size() != 0);
    item = pending.pop_front();
  endtask

  // EPN routing uses actual monitor-local identity plus an unambiguous key.
  // At most one outstanding transfer of a given endpoint/direction is legal.
  task ocp_wait_epn_completion(logic [6:0] address, logic [3:0] endpoint,
      svt_usb_transfer::transfer_type_enum transfer_type,
      longint unsigned floor, time timeout, output usb_ocp_event result);
    bit done;
    int match_index;
    longint unsigned version;
    result = null;
    done = 0;
    fork
      begin
        fork
          begin
            while (result == null) begin
              version = completion_version;
              match_index = -1;
              foreach (completions[i])
                if (completions[i].order >= floor &&
                    completions[i].transfer_start_order >= floor &&
                    completions[i].address === address &&
                    completions[i].endpoint === endpoint &&
                    completions[i].transfer_type === transfer_type) begin
                  if (match_index != -1)
                    `uvm_fatal("OCP_CORRELATION", "Ambiguous EPN monitor completion")
                  match_index = i;
                end
              if (match_index != -1) begin
                result = completions[match_index];
                completions.delete(match_index);
                completion_version++;
              end else wait (completion_version != version);
            end
            done = 1;
          end
          begin #(timeout); end
        join_any
        disable fork;
      end
    join
    if (!done) `uvm_fatal("OCP_CORRELATION", "EPN monitor completion timeout")
  endtask

  function int ocp_find_completion(logic [6:0] address, logic [7:0] setup[8],
                                   longint unsigned floor);
    int match_index;
    match_index = -1;
    foreach (completions[i]) begin
      if (completions[i].order >= floor &&
          completions[i].transfer_start_order >= floor &&
          completions[i].address === address &&
          completions[i].endpoint === 0 && completions[i].setup === setup) begin
        if (match_index != -1)
          `uvm_fatal("OCP_CORRELATION", "Ambiguous control-transfer completion identity")
        match_index = i;
      end
    end
    return match_index;
  endfunction

  // Preserve other devices' completions until their own waiters consume them.
  // A monotonic version wakes waiters even when the queue size returns to its
  // prior value after another waiter consumes an entry.
  task ocp_wait_completion(logic [6:0] address, logic [7:0] setup[8],
                           longint unsigned floor, time timeout,
                           output usb_ocp_event result);
    bit done;
    int match_index;
    longint unsigned version;
    result = null;
    done = 0;
    fork
      begin
        fork
          begin
            while (result == null) begin
              version = completion_version;
              match_index = ocp_find_completion(address,setup,floor);
              if (match_index != -1) begin
                if (match_index != 0) reordered_completions++;
                result = completions[match_index];
                completions.delete(match_index);
                completion_version++;
              end else
                wait (completion_version != version);
            end
            if (result.order < floor || result.transfer_start_order < floor ||
                result.address !== address ||
                result.endpoint !== 0 || result.setup !== setup)
              `uvm_fatal("OCP_CORRELATION", "Unmatched control-transfer completion")
            done = 1;
          end
          begin
            #(timeout);
          end
        join_any
        disable fork;
      end
    join
    if (!done) `uvm_fatal("OCP_CORRELATION", "Control-transfer completion timeout")
  endtask

  function bit ocp_check_drained();
    if (pending.size() != 0 || completions.size() != 0 ||
        started_at.num() != 0 || transfer_starts != transfer_count) return 0;
    foreach (outstanding_axi[i]) if (outstanding_axi[i] != 0) return 0;
    return 1;
  endfunction

  // Entry barriers must not demand that the continuously polling AXI actors
  // stop, or that unpublished partial-image bytes have already been consumed.
  function bit ocp_check_usb_idle();
    return pending.size() == 0 && completions.size() == 0 &&
           started_at.num() == 0 && transfer_starts == transfer_count;
  endfunction
endclass
