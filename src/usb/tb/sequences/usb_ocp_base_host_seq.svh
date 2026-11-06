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

class usb_ocp_base_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_ocp_base_host_seq)
  typedef logic [7:0] bytes_t[$];
  usb_ocp_base_env_cfg ocp_cfg;
  usb_ocp_observer observer;
  rand logic [7:0] image[];
  int unsigned max_read;
  int unsigned max_write;
  logic [7:0] interface_number;
  logic [7:0] cms;
  int unsigned cms_count;
  int unsigned fifo_depth;
  int unsigned fifo_max;

  function new(string name = "usb_ocp_base_host_seq");
    super.new(name);
  endfunction

  // One bounded submission, exact routed response, and independently copied
  // protocol-monitor completion. No first-ended-event matching is used.
  task ocp_do_check_control(int device, logic [7:0] bm, logic [7:0] request,
                            logic [15:0] value, logic [15:0] index,
                            logic [15:0] length, bytes_t write_data,
                            output bytes_t read_data);
    svt_usb_transfer tr;
    uvm_sequence_item response;
    usb_ocp_event observed;
    logic [7:0] setup[8];
    logic [6:0] addr;
    longint unsigned floor;
    int payload_size;
    bit done;
    logic [`SVT_USB_RESULTS_STATUS_SIZE-1:0] allowed_results;
    if (device < 0 || device > 2 || observer == null || ocp_cfg == null)
      `uvm_fatal("OCP_HOST", "Missing host context or invalid stable device slot")
    if (!bm[7] && write_data.size() != length)
      `uvm_fatal("OCP_HOST", "OUT payload does not match wLength")
    addr = usb_cfg.remote_device_cfg[device].device_address;
    setup = '{bm,request,value[7:0],value[15:8],index[7:0],index[15:8],
              length[7:0],length[15:8]};
    floor = observer.next_order;
    tr = svt_usb_transfer::type_id::create("ocp_control_request");
    payload_size = write_data.size();
    done = 0;
    read_data.delete();
    `uvm_info("OCP_HOST_START",$sformatf(
      "Submitting slot=%0d addr=%0d ep=0 setup=%p order_floor=%0d",
      device,addr,setup,floor),UVM_LOW)
    fork
      begin
        fork
          begin
            start_item(tr,-1,p_sequencer.xfer_sequencer);
            tr.cfg = usb_cfg;
            tr.fix_anchors(device,0,0);
            if (!bm[7]) begin
              tr.payload = svt_usb_payload::type_id::create("ocp_out_payload");
              tr.payload.data = new[payload_size];
            end
            if (!tr.randomize() with {
                  xfer_type == svt_usb_transfer::CONTROL_TRANSFER;
                  device_address == local::addr;
                  setup_data_bmrequesttype_dir == local::bm[7];
                  setup_data_bmrequesttype_type == local::bm[6:5];
                  setup_data_bmrequesttype_recipient == local::bm[4:0];
                  setup_data_brequest == local::request;
                  setup_data_w_value == local::value;
                  setup_data_w_index == local::index;
                  setup_data_w_length == local::length;
                  payload_start_ix == 0;
                  payload_intended_byte_count == local::length;
                  if (!local::bm[7]) {
                    payload.data.size() == local::payload_size;
                    foreach (payload.data[i]) payload.data[i] == local::write_data[i];
                  }
                }) `uvm_fatal("OCP_HOST", "Control transfer randomization failed")
            finish_item(tr);
            get_response(response,tr.get_transaction_id());
            if (response == null || response.get_sequence_id() != tr.get_sequence_id() ||
                response.get_transaction_id() != tr.get_transaction_id())
              `uvm_fatal("OCP_HOST", "Wrong routed UVM response")
            observer.ocp_wait_completion(addr,setup,floor,ocp_cfg.control_transfer_timeout,observed);
            done = 1;
          end
          begin #(ocp_cfg.control_transfer_timeout); end
        join_any
        disable fork;
      end
    join
    if (!done) `uvm_fatal("OCP_HOST", "Bounded control submission/completion timed out")
    allowed_results = 0;
    if (!bm[7]) allowed_results[5] = 1;
    if (!observed.transfer_ok || (observed.results & ~allowed_results) !== 0)
      `uvm_fatal("OCP_HOST", "VIP reported unsuccessful control completion")
    if (bm[7]) read_data = observed.bytes;
    else begin
      if (observed.bytes.size() != write_data.size())
        `uvm_fatal("OCP_HOST", "Completed OUT byte count differs from request")
      foreach (write_data[i])
        if (observed.bytes[i] !== write_data[i])
          `uvm_fatal("OCP_HOST", "Completed OUT payload differs from independently prepared image")
    end
    `uvm_info("OCP_HOST",$sformatf("Completed slot=%0d addr=%0d setup=%p bytes=%0d",
              device,addr,setup,observed.bytes.size()),UVM_MEDIUM)
  endtask

  task ocp_do_check_enumeration(int device);
    bytes_t data;
    bytes_t empty;
    int total;
    // Only the device being enumerated occupies address zero. Its own slot
    // transitions parking -> default -> assigned; other slot identities stay
    // unchanged and are never used as aliases to switch traffic.
    if (device != 0) begin
      usb_cfg.remote_device_cfg[device].device_address = 0;
      host_agent.reconfigure(usb_cfg);
    end
    ocp_do_check_control(device,8'h80,6,16'h0100,0,18,empty,data);
    if (data.size() != 18 || data[0] !== 18 || data[1] !== 1 || data[7] !== 64)
      `uvm_fatal("OCP_ENUM", "Invalid EP0 device descriptor")
    ocp_do_check_control(device,0,5,16'(ocp_cfg.assigned_address[device]),0,0,empty,data);
    // USB 2.0 9.2.6.3: reuse the VIP recovery guard for SET_ADDRESS.
    #(usb_cfg.trstrcy * 1ps);
    usb_cfg.remote_device_cfg[device].device_address = ocp_cfg.assigned_address[device];
    host_agent.reconfigure(usb_cfg);
    ocp_do_check_control(device,8'h80,6,16'h0100,0,18,empty,data);
    ocp_do_check_control(device,8'h80,6,16'h0200,0,9,empty,data);
    if (data.size() != 9 || data[0] !== 9 || data[1] !== 2)
      `uvm_fatal("OCP_ENUM", "Invalid configuration header")
    total = {data[3],data[2]};
    if (total < 9 || total > 256)
      `uvm_fatal("OCP_ENUM", "Configuration length outside bringup bound")
    ocp_do_check_control(device,8'h80,6,16'h0200,0,16'(total),empty,data);
    if (data.size() != total)
      `uvm_fatal("OCP_ENUM", "Short configuration descriptor")
    if (device == 1) ocp_check_discovery(data);
    if (device == 0) begin
      ocp_do_check_control(0,8'ha0,6,16'h2900,0,9,empty,data);
      if (data.size() != 9 || data[2] !== 2)
        `uvm_fatal("OCP_ENUM", "Hub does not report two ports")
    end
    ocp_do_check_control(device,8'h80,8,0,0,1,empty,data);
    if (data.size() != 1 || data[0] !== 0)
      `uvm_fatal("OCP_ENUM", "Device unexpectedly configured before SET_CONFIGURATION")
    ocp_do_check_control(device,0,9,1,0,0,empty,data);
    ocp_do_check_control(device,8'h80,8,0,0,1,empty,data);
    if (data.size() != 1 || data[0] !== 1)
      `uvm_fatal("OCP_ENUM", "SET_CONFIGURATION did not take effect")
  endtask

  task ocp_do_check_port(int port);
    bytes_t data;
    bytes_t empty;
    time deadline;
    ocp_do_check_control(0,8'h23,3,8,16'(port),0,empty,data);
    #(usb_cfg.tattdb * 1ps);
    ocp_do_check_control(0,8'ha3,0,0,16'(port),4,empty,data);
    if (data.size() != 4 || data[0][0] !== 1'b1 || data[1][0] !== 1'b1)
      `uvm_fatal("OCP_PORT", "Downstream port not connected/powered")
    ocp_do_check_control(0,8'h23,1,16,16'(port),0,empty,data);
    ocp_do_check_control(0,8'h23,3,4,16'(port),0,empty,data);
    deadline = $time + 100ms;
    do begin
      #(usb_cfg.tdrst * 1ps);
      ocp_do_check_control(0,8'ha3,0,0,16'(port),4,empty,data);
      if (data.size() != 4) `uvm_fatal("OCP_PORT", "Short port status")
      if (data[0][4] === 0 && data[0][1] === 1 && data[2][4] === 1) break;
      if ($time >= deadline) `uvm_fatal("OCP_PORT", "Downstream reset completion timeout")
    end while (1);
    if (data[1][2:1] !== 2'b10)
      `uvm_fatal("OCP_PORT", "Downstream device did not negotiate high speed")
    ocp_do_check_control(0,8'h23,1,20,16'(port),0,empty,data);
    #(usb_cfg.trstrcy * 1ps);
  endtask

  function void ocp_check_discovery(bytes_t data);
    int pos;
    int interfaces;
    int functions;
    bit associated;
    pos = 9;
    interfaces = 0;
    functions = 0;
    associated = 0;
    while (pos < data.size()) begin
      if (data[pos] < 2 || pos+data[pos] > data.size())
        `uvm_fatal("OCP_DISCOVERY", "Malformed descriptor chain")
      if (data[pos+1] == 4) begin
        associated = 0;
        if (data[pos] != 9) `uvm_fatal("OCP_DISCOVERY", "Malformed interface")
        if (data[pos+5] === 8'hef && data[pos+6] === 8'h08 && data[pos+7] === 1) begin
          if (data[pos+3] !== 0 || data[pos+4] !== 0)
            `uvm_fatal("OCP_DISCOVERY", "OCP interface must use EP0 only, alternate zero")
          interfaces++;
          associated = 1;
          interface_number = data[pos+2];
        end
      end
      if (associated && data[pos+1] == OCP_USB_FUNC_DESC_TYPE) begin
        if (data[pos] != OCP_USB_FUNC_DESC_LEN || data[pos+2] !== OCP_USB_FUNC_DESC_SUBTYPE ||
            data[pos+3] !== 0 || {data[pos+9],data[pos+8]} !== OCP_USB_BCD_VERSION_1P1)
          `uvm_fatal("OCP_DISCOVERY", "Malformed OCP functional descriptor")
        max_write = {data[pos+5],data[pos+4]};
        max_read = {data[pos+7],data[pos+6]};
        functions++;
      end
      pos += data[pos];
    end
    if (interfaces != 1 || functions != 1 ||
        max_read < OCP_USB_MIN_TRANSFER_SIZE || max_write < OCP_USB_MIN_TRANSFER_SIZE)
      `uvm_fatal("OCP_DISCOVERY", "Missing/duplicate OCP interface, descriptor, or invalid limits")
  endfunction

  task ocp_do_check_read(ocp_cmd_t cmd, output bytes_t data);
    bytes_t empty;
    if (max_read == 0) `uvm_fatal("OCP_DISCOVERY", "Read before USB discovery")
    ocp_do_check_control(1,8'ha1,OCP_BREQUEST_XFER,16'(cmd),
                         {8'b0,interface_number},16'(max_read),empty,data);
  endtask

  task ocp_do_check_write(ocp_cmd_t cmd, bytes_t data);
    bytes_t response;
    if (max_write == 0 || data.size() > max_write)
      `uvm_fatal("OCP_DISCOVERY", "Write exceeds discovered limit")
    ocp_do_check_control(1,8'h21,OCP_BREQUEST_XFER,16'(cmd),
                         {8'b0,interface_number},16'(data.size()),data,response);
  endtask

  task ocp_do_check_fifo_control(logic [7:0] selected, int unsigned words);
    bytes_t data;
    data = '{selected,0,8'(words),8'(words>>8),8'(words>>16),8'(words>>24)};
    ocp_do_check_write(OCP_CMD_INDIRECT_FIFO_CTRL,data);
  endtask

  task ocp_do_check_recovery();
    bytes_t data;
    bytes_t chunk;
    logic [15:0] caps;
    int words;
    int chunk_words;
    int chunk_limit;
    int offset;
    bit found;
    time deadline;
    time service_gap;
    deadline = $time + ocp_cfg.control_transfer_timeout;
    do begin
      if ($time >= deadline)
        `uvm_fatal("OCP_READY", "Recovery Mode readiness timeout")
      ocp_do_check_read(OCP_CMD_DEVICE_STATUS,data);
      if (data.size() < OCP_SPEC_MIN_LEN_DEVICE_STATUS)
        `uvm_fatal("OCP_READY", "Short DEVICE_STATUS during readiness discovery")
      if ($time >= deadline)
        `uvm_fatal("OCP_READY", "Recovery Mode readiness timeout")
      if (data[OCP_OFF_DS_STATUS] === OCP_DEVICE_STATUS_RECOVERY_MODE) break;
      #10us;
    end while (1);
    `uvm_info("OCP_READY", "USB DEVICE_STATUS reports Recovery Mode before PROT_CAP",UVM_LOW)
    ocp_do_check_read(OCP_CMD_PROT_CAP,data);
    if (data.size() != OCP_SPEC_LEN_PROT_CAP)
      `uvm_fatal("OCP_HOST", "Invalid PROT_CAP length")
    foreach (OCP_SPEC_PROT_CAP_MAGIC[i])
      if (data[i] !== OCP_SPEC_PROT_CAP_MAGIC[i])
        `uvm_fatal("OCP_HOST", "Invalid OCP magic")
    caps = {data[11],data[10]};
    if (!caps[OCP_CAP_INDIRECT_FIFO] || !caps[OCP_CAP_PUSH_C_IMAGE] || data[12] == 0)
      `uvm_fatal("OCP_HOST", "FIFO recovery support is required, not skipped")
    cms_count = data[12];
    found = 0;
    for (int i = 0; i < cms_count; i++) begin
      ocp_do_check_fifo_control(8'(i),0);
      ocp_do_check_read(OCP_CMD_INDIRECT_FIFO_STATUS,data);
      if (data.size() != OCP_SPEC_LEN_INDIRECT_FIFO_STATUS)
        `uvm_fatal("OCP_HOST", "Invalid FIFO status length")
      if (data[1] === OCP_REGION_RECOVERY_CODE_WO) begin
        cms = 8'(i);
        fifo_depth = {data[15],data[14],data[13],data[12]};
        fifo_max = {data[19],data[18],data[17],data[16]};
        found = (fifo_depth > 0 && fifo_max > 0 && data[0] === OCP_IFS_EMPTY_MASK);
        break;
      end
    end
    if (!found) `uvm_fatal("OCP_HOST", "No usable empty recovery FIFO CMS discovered")
    words = $urandom_range(17,64);
    if (words > fifo_depth/2) words = (fifo_depth > 1) ? fifo_depth/2 : 1;
    if (!randomize(image) with { image.size() == local::words*4; })
      `uvm_fatal("OCP_HOST", "Small image randomization failed")
    chunk_limit = max_write/4;
    if (chunk_limit > fifo_max) chunk_limit = fifo_max;
    if (chunk_limit > fifo_depth) chunk_limit = fifo_depth;
    if (chunk_limit == 0) `uvm_fatal("OCP_HOST", "No legal DWORD-aligned chunk")
    `uvm_info("OCP_IMAGE",$sformatf("image_bytes=%0d CMS=%0d depth=%0d max_chunk_words=%0d",
              image.size(),cms,fifo_depth,chunk_limit),UVM_LOW)
    ocp_do_check_fifo_control(cms,words);
    offset = 0;
    while (offset < words) begin
      chunk_words = $urandom_range(1,chunk_limit);
      if (chunk_words > words-offset) chunk_words = words-offset;
      chunk.delete();
      for (int i = 0; i < chunk_words*4; i++) chunk.push_back(image[offset*4+i]);
      ocp_do_check_write(OCP_CMD_INDIRECT_FIFO_DATA,chunk);
      service_gap = $urandom_range(0,20)*1us;
      `uvm_info("OCP_CHUNK",$sformatf("offset_words=%0d chunk_words=%0d gap=%0t",
                offset,chunk_words,service_gap),UVM_LOW)
      offset += chunk_words;
      #(service_gap);
    end
    deadline = $time + 100ms;
    do begin
      ocp_do_check_read(OCP_CMD_DEVICE_STATUS,data);
      if (data.size() < OCP_SPEC_MIN_LEN_DEVICE_STATUS)
        `uvm_fatal("OCP_HOST", "Short DEVICE_STATUS")
      if (data[0] === OCP_DEVICE_STATUS_RECOVERY_PENDING) break;
      if ($time >= deadline) `uvm_fatal("OCP_HOST", "Recovery Pending timeout")
      #10us;
    end while (1);
    ocp_do_check_read(OCP_CMD_INDIRECT_FIFO_STATUS,data);
    if (data[0] !== OCP_IFS_EMPTY_MASK)
      `uvm_fatal("OCP_HOST", "FIFO not empty at Recovery Pending")
    chunk = '{cms,OCP_RC_IMAGE_SEL_CMS,OCP_RC_ACTIVATE_CODE};
    ocp_do_check_write(OCP_CMD_RECOVERY_CTRL,chunk);
    deadline = $time + 100ms;
    do begin
      ocp_do_check_read(OCP_CMD_DEVICE_STATUS,data);
      if (data[0] === OCP_DEVICE_STATUS_RUNNING_RECOVERY) break;
      if ($time >= deadline) `uvm_fatal("OCP_HOST", "Emulated final status timeout")
      #10us;
    end while (1);
    ocp_do_check_read(OCP_CMD_RECOVERY_CTRL,data);
    if (data.size() != 3 || data[0] !== cms || data[1] !== OCP_RC_IMAGE_SEL_CMS || data[2] !== 0)
      `uvm_fatal("OCP_HOST", "Activation not cleared through USB")
    ocp_do_check_read(OCP_CMD_RECOVERY_STATUS,data);
    if (data.size() != 2 || data[0][3:0] !== OCP_RECOVERY_STATUS_SUCCESS)
      `uvm_fatal("OCP_HOST", "Emulated firmware recovery status not successful")
  endtask

  task body();
    svt_usb_protocol_service_20_sof_on_sequence sof_on;
    svt_usb_protocol_service_20_sof_off_sequence sof_off;
    if (ocp_cfg == null || observer == null)
      `uvm_fatal("OCP_HOST", "Missing host configuration/observer")
    resolve_host_context(1);
    `uvm_info("OCP_TIMING", $sformatf(
      "Scaled USB timers: reset=%0t debounce=%0t reset/address_recovery=%0t",
      usb_cfg.tdrst * 1ps, usb_cfg.tattdb * 1ps, usb_cfg.trstrcy * 1ps), UVM_LOW)
    wait_for_link_enabled(ocp_cfg.link_timeout);
    sof_on = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("ocp_sof_on");
    sof_on.start(p_sequencer.prot_service_sequencer);
    #(usb_cfg.trstrcy * 1ps);
    ocp_do_check_enumeration(0);
    for (int device = 1; device < 3; device++) begin
      ocp_do_check_port(device);
      ocp_do_check_enumeration(device);
    end
    ocp_do_check_recovery();
    sof_off = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("ocp_sof_off");
    sof_off.start(p_sequencer.prot_service_sequencer);
    completed = 1;
    ocp_cfg.actor_finished[0] = 1;
  endtask
endclass
