// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_protocol_stall_model extends uvm_object;
  `uvm_object_utils(usb_ocp_protocol_stall_model)
  typedef logic [7:0] bytes_t[$];
  // OCP 1.1 9.1/9.2: a write to RO PROT_CAP is error 1, not length error 3.
  localparam logic [7:0] WRITE_RO_ERROR = 8'h01;
  localparam logic [7:0] CLEAR_SETUP[8] =
    '{8'h02,8'h01,8'h00,8'h00,8'h00,8'h00,8'h00,8'h00};
  logic [6:0] address;
  logic [7:0] setup[8];
  bytes_t write_data;
  int unsigned epoch;
  int unsigned generation;
  longint unsigned floor;
  longint unsigned setup_order;
  longint unsigned stall_order;
  longint unsigned clear_order;
  int unsigned clear_generation;
  int unsigned status_reads;
  int unsigned peer_controls;
  int unsigned peer_crosschecks;
  int unsigned peer_generation[$];
  longint unsigned peer_setup_orders[$];
  longint unsigned peer_status_orders[$];
  longint unsigned peer_native_orders[$];
  bit armed;
  bit setup_seen;
  bit stall_seen;
  bit native_checked;
  bit invalid_status_completed;
  bit clear_seen;
  bit clear_native_checked;
  bit finished;
  bytes_t accepted_prefix;
  bytes_t capabilities;
  bytes_t identity;
  bytes_t indirect;
  bit identity_seen;
  bit indirect_seen;
  int unsigned capability_reads;
  int unsigned identity_reads;
  int unsigned indirect_reads;
  int unsigned id_written;
  logic [7:0] id_expected[24];
  bit negative_owner;
  bit negative_status;
  bit negative_rtc;
  bit negative_peer;
  bit negative_prefix;
  bit negative_stage;
  int unsigned firmware_clears;
  // Exactly two legal INDIRECT_CTRL probes: baseline and rediscovery.
  // A negative outcome is an attempted access, never restored support.
  typedef struct {
    logic [6:0] address;
    logic [7:0] setup[8];
    int unsigned epoch;
    int unsigned generation;
    int unsigned max_packet;
    longint unsigned floor;
    longint unsigned setup_order;
    longint unsigned stall_order;
    longint unsigned clear_order;
    int unsigned clear_generation;
    int unsigned status_reads;
    int unsigned status_crosschecks;
    int unsigned firmware_clears;
    bit planned;
    bit setup_seen;
    bit data_ended;
    bit data_error;
    bit stall_seen;
    bit status_completed;
    bit native_checked;
    bit payload_valid;
    bit clear_seen;
    bit clear_native_checked;
    bit finished;
    bytes_t prefix;
    bytes_t data;
  } probe_t;
  probe_t probes[2];
  int active_probe = -1;
  int unsigned probe_attempts = 0;
  int unsigned probe_stalls = 0;
  int unsigned probe_successes = 0;
  bit protocol_pass = 1;

  function new(string name = "usb_ocp_protocol_stall_model");
    uvm_cmdline_processor cli;
    string args[$];
    super.new(name);
    cli = uvm_cmdline_processor::get_inst();
    cli.get_args(args);
    foreach (args[i])
      if (uvm_is_match("+usb_ocp_stall_negative_*",args[i]) &&
          !(args[i] inside {
            "+usb_ocp_stall_negative_owner", "+usb_ocp_stall_negative_status",
            "+usb_ocp_stall_negative_rtc", "+usb_ocp_stall_negative_peer",
            "+usb_ocp_stall_negative_prefix", "+usb_ocp_stall_negative_stage"}))
        `uvm_fatal("OCP_STALL_GUARD", "Unknown protocol STALL private control")
    negative_owner = $test$plusargs("usb_ocp_stall_negative_owner");
    negative_status = $test$plusargs("usb_ocp_stall_negative_status");
    negative_rtc = $test$plusargs("usb_ocp_stall_negative_rtc");
    negative_peer = $test$plusargs("usb_ocp_stall_negative_peer");
    negative_prefix = $test$plusargs("usb_ocp_stall_negative_prefix");
    negative_stage = $test$plusargs("usb_ocp_stall_negative_stage");
    foreach (probes[i]) begin
      probes[i].planned = 0;
      probes[i].setup_seen = 0;
      probes[i].data_ended = 0;
      probes[i].data_error = 0;
      probes[i].stall_seen = 0;
      probes[i].status_completed = 0;
      probes[i].native_checked = 0;
      probes[i].payload_valid = 0;
      probes[i].clear_seen = 0;
      probes[i].clear_native_checked = 0;
      probes[i].finished = 0;
      probes[i].clear_generation = 0;
      probes[i].status_reads = 0;
      probes[i].status_crosschecks = 0;
      probes[i].firmware_clears = 0;
    end
  endfunction

  function void ocp_configure_probe(int index, logic [6:0] addr,
      logic [7:0] iface, int unsigned max_read, int unsigned max_packet,
      int unsigned current_epoch, int unsigned next_generation,
      longint unsigned order_floor);
    if (!(index inside {0,1}) || active_probe != -1 ||
        max_read < OCP_USB_MIN_TRANSFER_SIZE || max_read > 65535 ||
        max_packet == 0 || next_generation == 0)
      `uvm_fatal("OCP_STALL_PROBE_OWNER", "Invalid or overlapping mandatory probe plan")
    if (probes[index].planned || (index == 0 && armed) ||
        (index == 1 && (!finished || !probes[0].finished || status_reads != 2)))
      `uvm_fatal("OCP_STALL_PROBE_OWNER", "Probe is duplicate or outside its baseline/rediscovery phase")
    probes[index].address = addr;
    probes[index].epoch = current_epoch;
    probes[index].generation = next_generation;
    probes[index].max_packet = max_packet;
    probes[index].floor = order_floor;
    // OCP 8.5.1 requires wMaxRdTransferSize, not the six-byte response size.
    probes[index].setup = '{8'ha1,OCP_BREQUEST_XFER,OCP_CMD_INDIRECT_CTRL,0,
      iface,0,8'(max_read),8'(max_read>>8)};
    probes[index].planned = 1;
    active_probe = index;
  endfunction

  function bit ocp_check_probe_owner(int device, usb_ocp_base_control c);
    if (active_probe < 0 || c == null) return 0;
    return device == 1 && probes[active_probe].planned &&
      c.address === probes[active_probe].address &&
      c.epoch == probes[active_probe].epoch &&
      c.generation == probes[active_probe].generation &&
      c.setup === probes[active_probe].setup;
  endfunction

  function bit ocp_check_terminal_owner(int device, usb_ocp_base_control c);
    return ocp_check_probe_owner(device,c) || ocp_check_owner(device,c);
  endfunction

  function void ocp_capture_probe_setup(usb_ocp_base_control c);
    int p;
    logic [7:0] expected_status_setup[8];
    p = active_probe;
    if (!probes[p].setup_seen) begin
      if (!ocp_check_probe_owner(1,c) || c.status_setup_order < probes[p].floor)
        `uvm_fatal("OCP_STALL_PROBE_OWNER", "Accepted mandatory probe SETUP differs from registered tuple/floor")
      probes[p].setup_seen = 1;
      probes[p].setup_order = c.status_setup_order;
      probe_attempts++;
      return;
    end
    if (!probes[p].stall_seen || !probes[p].native_checked)
      `uvm_fatal("OCP_STALL_PROBE_RECOVERY", "New SETUP before owned probe/native retirement")
    if (probes[p].clear_generation == 0) begin
      if (c.address !== probes[p].address || c.epoch != probes[p].epoch ||
          c.generation != probes[p].generation+1 || c.setup !== CLEAR_SETUP)
        `uvm_fatal("OCP_STALL_PROBE_RECOVERY", "Next accepted SETUP after probe STALL must be planned EP0 CLEAR_FEATURE")
      probes[p].clear_generation = c.generation;
      probes[p].clear_order = c.status_setup_order;
      return;
    end
    expected_status_setup = probes[p].setup;
    expected_status_setup[2] = OCP_CMD_DEVICE_STATUS;
    if (!probes[p].clear_seen || !probes[p].clear_native_checked ||
        probes[p].status_reads >= 2 || c.address !== probes[p].address ||
        probes[p].status_reads != probes[p].status_crosschecks ||
        c.epoch != probes[p].epoch ||
        c.generation != probes[p].clear_generation+1+probes[p].status_reads ||
        c.setup !== expected_status_setup)
      `uvm_fatal("OCP_STALL_PROBE_RTC", "Probe recovery requires exactly two subsequent owned DEVICE_STATUS reads")
  endfunction

  // Called only after the existing predictor accepts a new DATA toggle/ACK.
  function void ocp_capture_probe_data(int device, usb_ocp_base_control c,
      int unsigned packet_bytes);
    if (!ocp_check_probe_owner(device,c)) return;
    if (probes[active_probe].data_ended) begin
      probes[active_probe].data_error = 1;
      protocol_pass = 0;
      `uvm_error("OCP_CONTROL_DATA_STAGE", "New accepted DATA after mandatory probe DATA termination; no valid-support credit")
    end
    probes[active_probe].data_ended =
      probes[active_probe].data_ended ||
      packet_bytes < probes[active_probe].max_packet || c.data.size() == c.ocp_get_length();
  endfunction

  function bit ocp_check_probe_stall(int device, usb_ocp_base_control c,
      usb_ocp_event token, usb_ocp_event item, usb_ocp_event candidate);
    int p;
    bit legal_stage;
    if (!ocp_check_probe_owner(device,c)) return 0;
    p = active_probe;
    legal_stage = token.pid == svt_usb_packet::IN && !probes[p].data_ended;
    // USB2 8.5.1/8.5.3.1 permit HS PING to initiate OUT STATUS.
    if (token.pid == svt_usb_packet::PING && probes[p].data_ended)
      legal_stage = 1;
    if (token.pid == svt_usb_packet::OUT && probes[p].data_ended &&
        candidate != null && candidate.pid == svt_usb_packet::DATA1 &&
        candidate.bytes.size() == 0 && candidate.host_tx === 1 &&
        candidate.packet_valid === 1) legal_stage = 1;
    if (!probes[p].setup_seen || probes[p].stall_seen || c.active !== 1 ||
        c.status_acked !== 0 || token.address !== probes[p].address ||
        token.endpoint !== 0 || token.order <= probes[p].setup_order ||
        item.host_tx !== 0 || item.packet_valid !== 1 ||
        item.order <= token.order || !legal_stage)
      `uvm_fatal("OCP_STALL_PROBE_STAGE", "Mandatory probe STALL lacks accepted SETUP and legal DATA/STATUS stage")
    probes[p].stall_seen = 1;
    probes[p].stall_order = item.order;
    probes[p].prefix = c.data;
    probe_stalls++;
    protocol_pass = 0;
    `uvm_error("OCP_STALL_MANDATORY", $sformatf(
      "Required INDIRECT_CTRL probe=%0d rejected by STALL addr=%0d epoch=%0d generation=%0d SETUP=%0d STALL=%0d accepted_prefix=%0d; attempted access, support not restored",
      p,probes[p].address,probes[p].epoch,probes[p].generation,
      probes[p].setup_order,probes[p].stall_order,probes[p].prefix.size()))
    return 1;
  endfunction

  function void ocp_check_native_stall(usb_ocp_event item,
      longint unsigned order_floor, longint unsigned accepted_setup_order,
      longint unsigned actual_stall_order, bytes_t prefix,
      int unsigned payload_bound);
    logic [`SVT_USB_RESULTS_STATUS_SIZE-1:0] allowed;
    allowed = 0;
    allowed[4] = 1;
    allowed[5] = 1;
    if (item.endpoint !== 0 || item.transfer_type != svt_usb_transfer::CONTROL_TRANSFER ||
        item.transfer_start_order < order_floor ||
        item.transfer_start_order >= accepted_setup_order ||
        item.order <= actual_stall_order || item.native_aborted !== 1 ||
        item.transfer_ok !== 0 || item.results[4] !== 1 ||
        (item.results & ~allowed) !== 0)
      `uvm_fatal("OCP_STALL_NATIVE", "Owned native end lacks legal wire STALL, ordered ABORTED/results[4] attribution")
    // VIP payload_byte_count is a payload-window size, not an ACK count.
    // For either aborted direction, validate only the real accepted prefix.
    if (item.bytes.size() < prefix.size() || item.bytes.size() > payload_bound)
      `uvm_fatal("OCP_STALL_PREFIX", "Native STALL payload does not represent the ACK-qualified prefix")
    foreach (prefix[i])
      if (item.bytes[i] !== prefix[i])
        `uvm_fatal("OCP_STALL_PREFIX", "Native STALL payload differs from ACK-qualified prefix")
  endfunction

  function bit ocp_check_clear_ready();
    if (active_probe >= 0)
      return probes[active_probe].stall_seen && probes[active_probe].native_checked &&
        probes[active_probe].clear_generation != 0;
    return armed && !finished && native_checked && clear_generation != 0;
  endfunction

  function bit ocp_check_clear_service();
    if (!ocp_check_clear_ready()) return 0;
    if (active_probe >= 0) return probes[active_probe].firmware_clears == 0;
    return firmware_clears == 0;
  endfunction

  function void ocp_capture_firmware_clear();
    if (!ocp_check_clear_service())
      `uvm_fatal("OCP_STALL_FIRMWARE", "Firmware clear is duplicate or lacks its accepted owned SETUP")
    if (active_probe >= 0) probes[active_probe].firmware_clears++;
    else firmware_clears++;
  endfunction

  function bit ocp_check_status_owned(usb_ocp_base_control c);
    logic [7:0] expected_status_setup[8];
    if (c == null) return 0;
    if (active_probe >= 0) begin
      expected_status_setup = probes[active_probe].setup;
      expected_status_setup[2] = OCP_CMD_DEVICE_STATUS;
      return probes[active_probe].stall_seen &&
        probes[active_probe].clear_generation != 0 &&
        c.address === probes[active_probe].address &&
        c.epoch == probes[active_probe].epoch &&
        c.setup === expected_status_setup &&
        c.generation inside {probes[active_probe].clear_generation+1,
                            probes[active_probe].clear_generation+2};
    end
    return armed && !finished;
  endfunction

  function void ocp_check_probe_retirement(int index);
    if (active_probe != index || !probes[index].setup_seen ||
        !probes[index].native_checked || probes[index].finished)
      `uvm_fatal("OCP_STALL_PROBE_INCOMPLETE", "Mandatory probe has unretired accepted/native obligations")
    if (probes[index].stall_seen) begin
      if (!probes[index].clear_seen || !probes[index].clear_native_checked ||
          probes[index].firmware_clears != 1 || probes[index].status_reads != 2 ||
          probes[index].status_crosschecks != 2)
        `uvm_fatal("OCP_STALL_PROBE_INCOMPLETE", "Negative mandatory probe lacks actual CLEAR_FEATURE and RTC retirement")
    end else if (!probes[index].status_completed)
      `uvm_fatal("OCP_STALL_PROBE_INCOMPLETE", "Successful mandatory probe lacks observed STATUS")
    probes[index].finished = 1;
    `uvm_info("OCP_STALL_PROBE_RESULT", $sformatf(
      "probe=%0d attempted=1 native_success=%0b native_STALL=%0b valid_support=%0b clear=%0b/%0b RTC_reads=%0d/%0d SETUP=%0d STALL=%0d CLEAR=%0d",
      index,probes[index].status_completed,probes[index].stall_seen,
      probes[index].payload_valid && !probes[index].stall_seen,
      probes[index].clear_seen,probes[index].clear_native_checked,
      probes[index].status_reads,probes[index].status_crosschecks,probes[index].setup_order,
      probes[index].stall_order,probes[index].clear_order), UVM_LOW)
    // Release only after actual successful or unsuccessful retirement checks.
    active_probe = -1;
  endfunction

  function void ocp_configure_request(logic [6:0] addr, logic [7:0] iface,
      int unsigned current_epoch, int unsigned next_generation,
      longint unsigned order_floor, bytes_t payload);
    if (armed || finished || active_probe != -1 || next_generation == 0 ||
        payload.size() != OCP_SPEC_LEN_PROT_CAP)
      `uvm_fatal("OCP_STALL_GUARD", "Invalid or duplicate owned write-RO plan")
    address = addr;
    epoch = current_epoch;
    generation = next_generation;
    floor = order_floor;
    write_data = payload;
    setup = '{8'h21,OCP_BREQUEST_XFER,OCP_CMD_PROT_CAP,0,iface,0,
              8'(payload.size()),0};
    armed = 1;
  endfunction

  function bit ocp_check_owner(int device, usb_ocp_base_control c);
    return armed && device == 1 && c.address === address &&
            c.epoch == epoch && c.generation == generation && c.setup === setup;
  endfunction

  function void ocp_capture_setup(int device, usb_ocp_base_control c);
    if (device == 1 && active_probe >= 0) begin
      ocp_capture_probe_setup(c);
      return;
    end
    if (!armed || finished || device != 1) return;
    if (!setup_seen) begin
      if (!ocp_check_owner(device,c) || c.status_setup_order < floor)
        `uvm_fatal("OCP_STALL_OWNER", "Accepted SETUP does not match registered address/epoch/generation")
      setup_seen = 1;
      setup_order = c.status_setup_order;
      return;
    end
    if (!clear_seen && clear_generation == 0) begin
      if ((!stall_seen && !invalid_status_completed) || !native_checked || c.epoch != epoch ||
          c.address !== address || c.generation != generation+1 ||
          c.setup !== CLEAR_SETUP)
        `uvm_fatal("OCP_STALL_RECOVERY", "First accepted replacement SETUP must be legal EP0 CLEAR_FEATURE after terminal STALL")
      clear_generation = c.generation;
      clear_order = c.status_setup_order;
    end
  endfunction

  // This is an allowance decision on an actual packet, never a fake event.
  function bit ocp_check_stall(int device, usb_ocp_base_control c,
      usb_ocp_event token, usb_ocp_event item, usb_ocp_event candidate);
    bit owner;
    if (ocp_check_probe_stall(device,c,token,item,candidate)) return 1;
    owner = ocp_check_owner(device,c);
    if (negative_owner) owner = 0;
    if (!owner) return 0;
    if (negative_stage || !setup_seen || c.active !== 1 || c.status_acked !== 0 ||
        token.endpoint !== 0 || token.address !== address ||
        token.pid == svt_usb_packet::SETUP ||
        !(token.pid inside {svt_usb_packet::OUT,svt_usb_packet::IN,svt_usb_packet::PING}) ||
        (token.pid == svt_usb_packet::IN && c.data.size() != c.ocp_get_length()) ||
        (token.pid != svt_usb_packet::IN && c.data.size() >= c.ocp_get_length()) ||
        (token.pid == svt_usb_packet::OUT &&
          (candidate == null ||
          !(candidate.pid inside {svt_usb_packet::DATA0,svt_usb_packet::DATA1}) ||
          candidate.host_tx !== 1 || candidate.packet_valid !== 1)) ||
        item.host_tx !== 0 || item.packet_valid !== 1 ||
        token.order <= setup_order || item.order <= token.order || stall_seen)
      `uvm_fatal("OCP_STALL_STAGE", "Owned STALL lacks a legal DATA/STATUS transaction and accepted SETUP")
    stall_seen = 1;
    stall_order = item.order;
    accepted_prefix = c.data;
    if (accepted_prefix.size() > write_data.size())
      `uvm_fatal("OCP_STALL_PREFIX", "ACK-qualified rejected-write prefix exceeds wLength")
    foreach (accepted_prefix[i])
      if (accepted_prefix[i] !== write_data[i])
        `uvm_fatal("OCP_STALL_PREFIX", "Accepted write-RO prefix differs from submitted bytes")
    `uvm_info("OCP_STALL_EXPECTED", $sformatf(
      "slot=1 addr=%0d epoch=%0d generation=%0d SETUP=%0d STALL=%0d token=%s accepted_prefix=%0d",
      address,epoch,generation,setup_order,stall_order,token.pid.name(),
      accepted_prefix.size()), UVM_LOW)
    return 1;
  endfunction

  function bit ocp_check_terminal_transfer(usb_ocp_event item);
    bytes_t checked_prefix;
    int p;
    if (active_probe >= 0 &&
        item.address === probes[active_probe].address &&
        item.setup === probes[active_probe].setup) begin
      p = active_probe;
      if (item.transfer_ok === 1 && item.results[4] === 0) return 0;
      if (probes[p].native_checked || !probes[p].stall_seen)
        `uvm_fatal("OCP_STALL_PROBE_OWNER", "Negative probe end lacks its unique actual wire STALL")
      ocp_check_native_stall(item,probes[p].floor,probes[p].setup_order,
        probes[p].stall_order,probes[p].prefix,
        {probes[p].setup[7],probes[p].setup[6]});
      probes[p].native_checked = 1;
      return 1;
    end
    if (!armed || item.address !== address || item.setup !== setup) return 0;
    // Incorrect success is checked by the ordinary packet/STATUS path, then
    // reported as a DUT error without preventing later recovery checks.
    if (item.transfer_ok === 1 && item.results[4] === 0) return 0;
    if (native_checked || !stall_seen)
      `uvm_fatal("OCP_STALL_NATIVE", "Owned terminal transfer lacks wire STALL and exact ABORTED/results[4] attribution")
    // VIP aborted OUT payload can include unaccepted bytes. Check its accepted
    // prefix only; the ACK ledger, not payload_byte_count, owns acceptance.
    ocp_check_native_stall(item,floor,setup_order,stall_order,
      accepted_prefix,write_data.size());
    if (negative_prefix) begin
      checked_prefix = accepted_prefix;
      // Append only to a private comparison operand, including a zero-prefix
      // DATA-stage STALL. Canonical ACK bytes and native actuals stay intact.
      checked_prefix.push_back(8'h00);
      if (item.bytes.size() < checked_prefix.size())
        `uvm_fatal("OCP_STALL_PREFIX", "Private prefix comparison requires a missing accepted byte")
      foreach (checked_prefix[i])
        if (item.bytes[i] !== checked_prefix[i])
          `uvm_fatal("OCP_STALL_PREFIX", "Private prefix comparison detects an extra/wrong accepted byte")
    end
    native_checked = 1;
    return 1;
  endfunction

  function void ocp_check_host_result(usb_ocp_event item);
    logic [`SVT_USB_RESULTS_STATUS_SIZE-1:0] allowed;
    int p;
    if (active_probe >= 0) begin
      p = active_probe;
      if (!probes[p].native_checked || item.address !== probes[p].address ||
          item.setup !== probes[p].setup || item.endpoint !== 0)
        `uvm_fatal("OCP_STALL_PROBE_OWNER", "Host consumed an unowned mandatory probe result")
      if (probes[p].stall_seen) begin
        ocp_check_native_stall(item,probes[p].floor,probes[p].setup_order,
          probes[p].stall_order,probes[p].prefix,
          {probes[p].setup[7],probes[p].setup[6]});
      end else if (!probes[p].status_completed || item.transfer_ok !== 1 ||
                  item.native_aborted !== 0 || item.results !== 0 ||
                  item.bytes !== probes[p].data)
        `uvm_fatal("OCP_STALL_NATIVE", "Successful mandatory probe lacks strict ordinary native payload/result checks")
      return;
    end
    allowed = 0;
    allowed[4] = 1;
    allowed[5] = 1;
    if (!native_checked || item.address !== address || item.setup !== setup ||
        !((item.native_aborted === 1 && item.transfer_ok === 0 && item.results[4] === 1) ||
          (invalid_status_completed && item.transfer_ok === 1 && item.results[4] === 0)) ||
        (item.results & ~allowed) !== 0)
      `uvm_fatal("OCP_STALL_NATIVE", "Host consumed an unowned or unchecked STALL completion")
  endfunction

  function void ocp_capture_control(int device, usb_ocp_base_control c,
      usb_ocp_base_control ocp, longint unsigned order);
    if (device == 1 && active_probe >= 0) begin
      if (ocp_check_probe_owner(device,c)) begin
        if (probes[active_probe].stall_seen || c.status_acked !== 1 ||
            !probes[active_probe].data_ended)
          `uvm_fatal("OCP_STALL_PROBE_STAGE", "Probe success cannot be credited after STALL")
        probes[active_probe].status_completed = 1;
      end else if (c.generation == probes[active_probe].clear_generation) begin
        if (c.data.size() != 0 || c.status_acked !== 1 || probes[active_probe].clear_seen)
          `uvm_fatal("OCP_STALL_PROBE_RECOVERY", "Probe clear requires one actual DATA1-ZLP STATUS")
        probes[active_probe].clear_seen = 1;
      end
      return;
    end
    if (!armed || finished) return;
    if (device == 1 && c.generation == generation) begin
      if (!ocp_check_owner(device,c) || c.data !== write_data)
        `uvm_fatal("OCP_STALL_PREFIX", "Incorrect successful write-RO completion still requires exact accepted OUT bytes")
      invalid_status_completed = 1;
      protocol_pass = 0;
      `uvm_error("OCP_STALL_MISSING", "Write to RO PROT_CAP incorrectly completed STATUS; recovery will continue")
    end
    if (device == 2 && ocp_check_owner(1,ocp) && ocp.active === 1 &&
        !stall_seen && c.status_setup_order > setup_order &&
        c.setup[0] === 8'h80 &&
        (c.setup[1] === 8'h08 ||
          (c.setup[1] === 8'h06 && c.ocp_get_value() === 16'h0100))) begin
      peer_controls++;
      peer_generation.push_back(c.generation);
      peer_setup_orders.push_back(c.status_setup_order);
      peer_status_orders.push_back(order);
    end
    if (device == 1 && c.generation == clear_generation && clear_generation != 0) begin
      if (c.data.size() != 0 || c.status_acked !== 1 || clear_seen)
        `uvm_fatal("OCP_STALL_RECOVERY", "CLEAR_FEATURE must complete one checked DATA1-ZLP STATUS")
      clear_seen = 1;
    end
  endfunction

  function void ocp_capture_crosscheck(int device, usb_ocp_base_control c,
      longint unsigned order);
    if (device == 1 && active_probe >= 0) begin
      if (ocp_check_probe_owner(device,c)) begin
        if (!probes[active_probe].status_completed || probes[active_probe].native_checked)
          `uvm_fatal("OCP_STALL_PROBE_OWNER", "Duplicate or premature successful probe native crosscheck")
        probes[active_probe].native_checked = 1;
        probe_successes++;
        if (probes[active_probe].payload_valid) indirect_reads++;
      end else if (c.generation == probes[active_probe].clear_generation)
        probes[active_probe].clear_native_checked = 1;
      else if (ocp_check_status_owned(c)) begin
        if (probes[active_probe].status_crosschecks >= 2 ||
            c.generation != probes[active_probe].clear_generation+1+
              probes[active_probe].status_crosschecks ||
            probes[active_probe].status_reads != probes[active_probe].status_crosschecks+1)
          `uvm_fatal("OCP_STALL_PROBE_RTC", "Duplicate or unobserved probe RTC native retirement")
        probes[active_probe].status_crosschecks++;
      end
      return;
    end
    if (armed && device == 1 && c.generation == generation &&
        invalid_status_completed) native_checked = 1;
    if (device == 2)
      foreach (peer_generation[i])
        if (peer_generation[i] == c.generation) begin
          peer_crosschecks++;
          peer_native_orders.push_back(order);
          peer_generation.delete(i);
          break;
        end
    if (device == 1 && clear_generation != 0 && c.generation == clear_generation)
      clear_native_checked = 1;
  endfunction

  function logic [7:0] ocp_check_protocol_error(usb_ocp_base_control c);
    logic [7:0] expected;
    expected = OCP_PROTOCOL_ERROR_NONE;
    if (!armed || finished) return expected;
    if (!clear_seen || !clear_native_checked ||
        c.address !== address || c.epoch != epoch ||
        c.generation <= clear_generation || status_reads >= 2)
      `uvm_fatal("OCP_STALL_RTC_ORDER", "DEVICE_STATUS does not follow owned CLEAR_FEATURE/native retirement")
    if (status_reads == 0) expected = WRITE_RO_ERROR;
    return expected;
  endfunction

  function void ocp_check_status(usb_ocp_base_control c);
    logic [7:0] expected;
    int p;
    if (active_probe >= 0) begin
      p = active_probe;
      if (!ocp_check_status_owned(c) || !probes[p].clear_seen ||
          !probes[p].clear_native_checked || probes[p].status_reads >= 2 ||
          c.generation != probes[p].clear_generation+1+probes[p].status_reads)
        `uvm_fatal("OCP_STALL_PROBE_RTC", "DEVICE_STATUS lacks its registered probe recovery order")
      expected = probes[p].status_reads == 0 ? WRITE_RO_ERROR : OCP_PROTOCOL_ERROR_NONE;
      if (c.data.size() != OCP_SPEC_MIN_LEN_DEVICE_STATUS)
        `uvm_fatal("OCP_STALL_PROBE_RTC", "Probe DEVICE_STATUS has malformed length")
      // OCP 9.1/9.2: unsupported-command error is 1; second read must clear.
      if (c.data[1] !== expected) begin
        protocol_pass = 0;
        `uvm_error("OCP_STALL_PROBE_RTC", $sformatf(
          "probe=%0d DEVICE_STATUS read=%0d protocol_code=%02h expected=%02h",
          p,probes[p].status_reads+1,c.data[1],expected))
      end
      probes[p].status_reads++;
      return;
    end
    expected = ocp_check_protocol_error(c);
    if (c.data.size() != OCP_SPEC_MIN_LEN_DEVICE_STATUS)
      `uvm_fatal("OCP_STALL_STATUS", "Owned DEVICE_STATUS has malformed length")
    if (c.data[1] !== expected) begin
      protocol_pass = 0;
      `uvm_error((status_reads == 0) ? "OCP_STALL_STATUS" : "OCP_STALL_RTC",
        $sformatf("OCP 1.1 9.1/9.2 read=%0d protocol_code=%02h expected=%02h",
                  status_reads+1,c.data[1],expected))
    end
    // Canonical spec check above always runs. Private operands cannot hide a
    // real DUT error by substituting a different expected protocol code.
    if (negative_status && status_reads == 0 && c.data[1] !== 8'h02)
      `uvm_error("OCP_STALL_STATUS", $sformatf(
        "Private error-code comparison mismatch: actual=%02h injected_parameter_value=02",
        c.data[1]))
    if (negative_rtc && status_reads == 1 && c.data[1] !== WRITE_RO_ERROR)
      `uvm_error("OCP_STALL_RTC", $sformatf(
        "Private RTC comparison mismatch: actual=%02h injected_not_cleared=01",
        c.data[1]))
    status_reads++;
  endfunction

  // Firmware programming is independent expectation evidence, not RDL data.
  function void ocp_capture_axi(usb_ocp_event item, string reg_name);
    int index;
    if (item.manager != 0 || !item.write_access ||
        $sscanf(reg_name,"DEVICE_ID_%d",index) != 1) return;
    if (index >= 0 && index < 6) begin
      if (item.response_ok !== 1 || item.bytes.size() != 4 || item.strobes.size() != 4)
        `uvm_fatal("OCP_STALL_ID", "Identity expectation lacks completed successful firmware programming")
      foreach (item.bytes[i]) begin
        if (item.strobes[i] !== 1)
          `uvm_fatal("OCP_STALL_ID", "Identity expectation requires all byte strobes")
        id_expected[index*4+i] = item.bytes[i];
      end
      id_written |= (1 << index);
    end
  endfunction

  function void ocp_check_identity(bytes_t data);
    if (id_written != 6'h3f || data.size() != 24)
      `uvm_fatal("OCP_STALL_ID", "Mandatory DEVICE_ID lacks firmware evidence or spec-sized UUID record")
    foreach (data[i])
      if (data[i] !== id_expected[i]) begin
        protocol_pass = 0;
        `uvm_error("OCP_STALL_ID", "DEVICE_ID changed from completed firmware programming")
      end
    identity = data;
    identity_seen = 1;
    identity_reads++;
  endfunction

  function void ocp_check_indirect(usb_ocp_base_control c);
    bytes_t data;
    bit valid;
    if (!ocp_check_probe_owner(1,c) || c.status_acked !== 1 ||
        probes[active_probe].stall_seen)
      `uvm_fatal("OCP_STALL_PROBE_OWNER", "INDIRECT_CTRL response has no registered successful probe context")
    data = c.data;
    probes[active_probe].data = data;
    valid = !probes[active_probe].data_error;
    if (data.size() != 6) begin
      protocol_pass = 0;
      `uvm_error("OCP_STALL_MANDATORY", "OCP 1.1 9.2 INDIRECT_CTRL length is not six")
      return;
    end
    foreach (data[i])
      if ($isunknown(data[i])) valid = 0;
    if (data[1] !== 0 || data[2][1:0] !== 0 ||
        !valid || data[0] >= capabilities[12]) begin
      valid = 0;
      protocol_pass = 0;
      `uvm_error("OCP_STALL_MANDATORY", "OCP 1.1 9.2 INDIRECT_CTRL has malformed CMS/reserved/IMO fields")
    end
    if (indirect_seen && data !== indirect) begin
      valid = 0;
      protocol_pass = 0;
      `uvm_error("OCP_STALL_SIDE_EFFECT", "Read-only invalid command changed INDIRECT_CTRL")
    end
    probes[active_probe].payload_valid = valid;
    if (valid && !indirect_seen) begin
      indirect = data;
      indirect_seen = 1;
    end
  endfunction

  function void ocp_check_capabilities(bytes_t data);
    capability_reads++;
    if (data[10][OCP_CAP_PUSH_C_IMAGE] && !data[10][OCP_CAP_INDIRECT_CTRL])
      protocol_pass = 0;
    if (!armed) begin capabilities = data; return; end
    if (data !== capabilities) begin
      protocol_pass = 0;
      `uvm_error("OCP_STALL_SIDE_EFFECT", "Rejected write changed PROT_CAP")
    end
  endfunction

  function void ocp_check_complete();
    bit peer_proved;
    peer_proved = peer_controls == 2 && peer_crosschecks == 2;
    if (negative_peer) peer_proved = 0;
    if (!peer_proved || peer_generation.size() != 0)
      `uvm_fatal("OCP_STALL_WINDOW", "Missing two checked/native-crosschecked device1 controls inside the owned in-flight error generation")
    foreach (peer_setup_orders[i])
      if (!(setup_order < peer_setup_orders[i] &&
            peer_setup_orders[i] < peer_status_orders[i] &&
            peer_status_orders[i] < peer_native_orders[i] &&
            peer_native_orders[i] < stall_order))
        `uvm_fatal("OCP_STALL_WINDOW", "Peer actual SETUP/STATUS/native orders do not lie inside the original error window")
    if (!setup_seen || !stall_seen || !native_checked || !clear_seen ||
        !clear_native_checked || firmware_clears != 1 || status_reads != 2 ||
        !identity_seen || !finished || capability_reads < 2 || identity_reads < 2 ||
        ((capabilities[10][OCP_CAP_INDIRECT_CTRL] ||
          capabilities[10][OCP_CAP_PUSH_C_IMAGE]) &&
          (probe_attempts != 2 || probe_attempts != probe_successes+probe_stalls ||
          !probes[0].finished || !probes[1].finished)) ||
        active_probe != -1)
      `uvm_fatal("OCP_STALL_INCOMPLETE", $sformatf(
        "Unreached obligations SETUP=%0b STALL=%0b native=%0b CLEAR=%0b/%0b firmware=%0d RTC_reads=%0d ID=%0b recovery=%0b; no reset/abort/drain substitution",
        setup_seen,stall_seen,native_checked,clear_seen,clear_native_checked,
        firmware_clears,status_reads,identity_seen,finished))
    `uvm_info("OCP_STALL_EVIDENCE", $sformatf(
      "addr=%0d epoch=%0d generation=%0d SETUP=%0d STALL=%0d CLEAR=%0d peer=%0d/%0d RTC_reads=%0d prefix=%0d peer_SETUP=%p peer_STATUS=%p peer_native=%p PROT_CAP_reads=%0d ID_reads=%0d INDIRECT_CTRL_reads=%0d",
      address,epoch,generation,setup_order,stall_order,clear_order,
      peer_controls,peer_crosschecks,status_reads,accepted_prefix.size(),
      peer_setup_orders,peer_status_orders,peer_native_orders,
      capability_reads,identity_reads,indirect_reads), UVM_LOW)
    `uvm_info("OCP_STALL_MANDATORY_RESULT", $sformatf(
      "INDIRECT_CTRL attempted=%0d native_success=%0d native_STALL=%0d valid_support=%0d restored=%0b protocol_pass=%0b; negative responses are attempted accesses, not valid mandatory support",
      probe_attempts,probe_successes,probe_stalls,indirect_reads,
      probes[1].finished && probes[1].payload_valid && !probes[1].stall_seen,
      protocol_pass), UVM_LOW)
  endfunction
endclass
