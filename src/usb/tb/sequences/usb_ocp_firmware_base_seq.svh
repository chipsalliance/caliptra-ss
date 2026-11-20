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

// Shared persistent MCU/SoC EP0 service. No host requests or recovery
// register operations are issued here. Standard EP0 mechanics follow
// usb_init_seq, without its fixed seven-request lifecycle.
class usb_ocp_firmware_base_seq extends usb_ocp_base_seq;
  `uvm_object_utils(usb_ocp_firmware_base_seq)
  typedef logic [7:0] bytes_t[$];
  int unsigned device = 1;
  usb_target_e csr_target;
  usb_target_e memory_target;
  logic [6:0] address_shadow;
  logic [7:0] configuration_shadow;
  logic [7:0] alternate_shadow;
  logic [31:0] command_shadow;
  int unsigned serviced;
  localparam logic [31:0] SETUP_BUFFER = 'h100;
  localparam logic [31:0] OUT_BUFFER = 'h140;
  localparam logic [31:0] IN_BUFFER = 'h180;

  function new(string name = "usb_ocp_firmware_base_seq");
    super.new(name);
    serviced = 0;
  endfunction

  function logic [31:0] ocp_get_mask(string reg_name, string field_name);
    uvm_reg r;
    uvm_reg_field f;
    r = csr_block_for(csr_target).get_reg_by_name(reg_name);
    if (r == null) `uvm_fatal("OCP_FIRMWARE", "Missing device register")
    f = r.get_field_by_name(field_name);
    return ral_field_mask(f);
  endfunction

  task ocp_read_csr(string reg_name, output logic [31:0] value);
    read32(csr_target,csr_offset(csr_target,reg_name),value);
  endtask

  task ocp_write_csr(string reg_name, logic [31:0] value);
    write32(csr_target,csr_offset(csr_target,reg_name),value);
  endtask

  task ocp_write_command(logic [31:0] w1c = 0);
    logic [31:0] value;
    uvm_reg r;
    r = csr_block_for(csr_target).get_reg_by_name("DEVCMDSTAT");
    value = command_shadow | ral_field_value(r.get_field_by_name("DEV_ADDR"),address_shadow);
    ocp_write_csr("DEVCMDSTAT",value | w1c);
  endtask

  task ocp_initialize_ep0();
    write32(memory_target,endpoint_list_base(),
            endpoint_entry(1'b1,1'b0,8,OUT_BUFFER));
    write32(memory_target,endpoint_list_base()+4,
            endpoint_entry(1'b0,1'b0,0,SETUP_BUFFER));
    write32(memory_target,endpoint_list_base()+8,
            endpoint_entry(1'b0,1'b0,0,IN_BUFFER));
  endtask

  virtual task ocp_initialize_controller();
    logic [31:0] command;
    time deadline;
    time poll_interval;
    address_shadow = 0;
    configuration_shadow = 0;
    for (int offset = 0; offset < ocp_cfg.endpoint_list_bytes(); offset += 4)
      write32(memory_target,endpoint_list_base()+offset,0);
    ocp_initialize_ep0();
    ocp_write_csr("EPLISTSTART",endpoint_list_base());
    ocp_write_csr("DATABUFSTART",0);
    deadline = $time + ocp_cfg.vbus_timeout;
    poll_interval = ocp_cfg.service_poll;
    do begin
      if (ocp_cfg.stop_requested === 1'b1)
        `uvm_fatal("OCP_TEARDOWN", "Teardown before device VBUS preparation")
      if ($time >= deadline) `uvm_fatal("OCP_VBUS", "Device VBUS timeout")
      ocp_read_csr("DEVCMDSTAT",command);
      if ($time >= deadline) `uvm_fatal("OCP_VBUS", "Device VBUS timeout")
      if ((command & ocp_get_mask("DEVCMDSTAT","VBUS_DEBOUNCED")) != 0) break;
      ocp_wait_service_interval(poll_interval,deadline,"OCP_VBUS","Device VBUS timeout");
      poll_interval = ocp_get_next_idle_poll(poll_interval);
    end while (1);
    command_shadow = ocp_get_mask("DEVCMDSTAT","DEV_EN") |
                     ocp_get_mask("DEVCMDSTAT","DCON");
    ocp_write_command();
    ocp_write_csr("INTEN",ocp_get_mask("INTEN","DEV_INT_EN") | 3);
    ocp_write_csr("INTSTAT",ocp_get_mask("INTSTAT","DEV_INT") | 3);
    ocp_cfg.prepared[device-1] = 1;
  endtask

  task ocp_send_ep0(bytes_t data);
    logic [31:0] word;
    if (data.size() > 64) `uvm_fatal("OCP_FIRMWARE", "Standard response exceeds EP0 buffer")
    for (int i = 0; i < data.size(); i += 4) begin
      word = 0;
      for (int j = 0; j < 4 && i+j < data.size(); j++)
        word[j*8+:8] = data[i+j];
      write32(memory_target,IN_BUFFER+i,word);
    end
    write32(memory_target,endpoint_list_base()+8,
            endpoint_entry(1'b1,1'b0,data.size(),IN_BUFFER));
    write32(memory_target,endpoint_list_base(),
            endpoint_entry(1'b1,1'b0,0,OUT_BUFFER));
  endtask

  virtual task ocp_do_check_owned_setup(logic [7:0] request_type,
      logic [7:0] request, logic [15:0] value, logic [15:0] index,
      logic [15:0] length, output bit handled);
    handled = 0;
  endtask

  task ocp_service_setup();
    usb_ocp_base_epn_profile profile;
    logic [31:0] word0;
    logic [31:0] word1;
    logic [7:0] request_type;
    logic [7:0] request;
    logic [15:0] value;
    logic [15:0] index;
    logic [15:0] length;
    bytes_t data;
    bit handled;
    read32(memory_target,SETUP_BUFFER,word0);
    read32(memory_target,SETUP_BUFFER+4,word1);
    request_type = word0[7:0];
    request = word0[15:8];
    value = word0[31:16];
    index = word1[15:0];
    length = word1[31:16];
    // OCP requests belong solely to hardware. In particular do not clear
    // SETUP, arm a response, or consume endpoint SRAM on its behalf.
    if (device == 1 && request_type inside {8'h21,8'ha1}) return;
    ocp_do_check_owned_setup(request_type,request,value,index,length,handled);
    if (handled) return;
    profile = ocp_cfg.ocp_get_epn_profile(device);
    ocp_write_csr("INTSTAT",ocp_get_mask("INTSTAT","EP0IN"));
    case (request)
      6: begin
        if (request_type !== 8'h80)
          `uvm_fatal("OCP_FIRMWARE", "Unexpected descriptor request type")
        if (profile != null)
          data = profile.ocp_prepare_descriptor(device,value);
        else
          data = usb_ocp_base_descriptors::ocp_prepare_descriptor(device,value);
        if (data.size() == 0) `uvm_fatal("OCP_FIRMWARE", "Unsupported descriptor")
        while (data.size() > length) void'(data.pop_back());
        command_shadow |= ocp_get_mask("DEVCMDSTAT","INTONNAK_CO");
        command_shadow &= ~ocp_get_mask("DEVCMDSTAT","INTONNAK_CI");
      end
      0: begin
        if (request_type !== 8'h80 || length !== 2 || value !== 0 || index !== 0)
          `uvm_fatal("OCP_FIRMWARE", "Malformed GET_STATUS")
        data = '{0,0};
      end
      5: begin
        if (request_type !== 0 || length !== 0 || index !== 0 ||
            value == 0 || value > 127)
          `uvm_fatal("OCP_FIRMWARE", "Malformed SET_ADDRESS")
      end
      8: begin
        if (request_type !== 8'h80 || length !== 1 || value !== 0 || index !== 0)
          `uvm_fatal("OCP_FIRMWARE", "Malformed GET_CONFIGURATION")
        data = '{configuration_shadow};
      end
      9: begin
        if (request_type !== 0 || length !== 0 || index !== 0 || value > 1)
          `uvm_fatal("OCP_FIRMWARE", "Malformed SET_CONFIGURATION")
        configuration_shadow = value[7:0];
        if (profile != null) begin
          alternate_shadow = 0;
          ocp_cfg.epn_enabled[device-1] = (value == 1 &&
            profile.transfer_type != USB_TRANSFER_TYPE_ISOCHRONOUS);
        end
      end
      svt_usb_types::GET_INTERFACE,svt_usb_types::SET_INTERFACE: begin
        if (profile == null ||
            configuration_shadow !== 1 || index !== 1)
          `uvm_fatal("OCP_EPN_INTERFACE", "Unsupported/unconfigured firmware interface")
        if (request == svt_usb_types::GET_INTERFACE) begin
          if (request_type !== 8'h81 || value !== 0 || length !== 1)
            `uvm_fatal("OCP_EPN_INTERFACE", "Malformed GET_INTERFACE")
          data = '{alternate_shadow};
        end else begin
          if (request_type !== 8'h01 || length !== 0 || value > 1 ||
              (value == 1 &&
               profile.transfer_type != USB_TRANSFER_TYPE_ISOCHRONOUS))
            `uvm_fatal("OCP_EPN_INTERFACE", "Unadvertised SET_INTERFACE")
          alternate_shadow = value[7:0];
          ocp_cfg.epn_enabled[device-1] = (value == 1 ||
            profile.transfer_type != USB_TRANSFER_TYPE_ISOCHRONOUS);
        end
      end
      default: `uvm_fatal("OCP_FIRMWARE", "Unimplemented standard request in bringup")
    endcase
    ocp_send_ep0(data);
    if (request == 5) address_shadow = value[6:0];
    // Address is programmed with an armed status IN, as in usb_init_seq.
    // W1C bits are explicit, not copied from a read of DEVCMDSTAT.
    ocp_write_command(ocp_get_mask("DEVCMDSTAT","SETUP"));
    serviced++;
  endtask

  virtual task ocp_connect_upstream();
  endtask

  // Called only after the owner's actual DEVCMDSTAT frontdoor detected DRES_C.
  virtual task ocp_do_check_reset_indication(logic [31:0] command);
  endtask

  virtual task body();
    usb_ocp_base_epn_service_seq epn_service;
    usb_ocp_base_epn_profile profile;
    profile = ocp_cfg.ocp_get_epn_profile(device);
    if (profile == null) begin
      ocp_do_standard_service();
      return;
    end
    epn_service = usb_ocp_base_epn_service_seq::type_id::create("epn_service");
    epn_service.profile = profile;
    epn_service.device = device;
    fork
      ocp_do_standard_service();
      epn_service.start(p_sequencer,this);
    join
    if (!epn_service.completed)
      `uvm_fatal("OCP_EPN_SERVICE", "Owned endpoint service returned incomplete")
  endtask

  task ocp_do_standard_service();
    logic [31:0] command;
    logic [31:0] interrupts;
    logic reset_was_set;
    logic reset_is_set;
    logic progress;
    int unsigned serviced_before;
    time deadline;
    time poll_interval;
    if (!(device inside {1,2})) `uvm_fatal("OCP_FIRMWARE", "Invalid device ownership")
    csr_target = (device == 1) ? USB_DEV0_CSR : USB_DEV1_CSR;
    memory_target = (device == 1) ? USB_DEV0_SRAM : USB_DEV1_SRAM;
    ocp_initialize_controller();
    ocp_connect_upstream();
    deadline = $time + ocp_cfg.actor_timeout;
    poll_interval = ocp_cfg.service_poll;
    reset_was_set = 0;
    while (!ocp_cfg.stop_requested) begin
      if ($time >= deadline) `uvm_fatal("OCP_FIRMWARE", "Persistent service exceeded lifecycle bound")
      progress = 0;
      serviced_before = serviced;
      ocp_read_csr("DEVCMDSTAT",command);
      reset_is_set = ((command & ocp_get_mask("DEVCMDSTAT","DRES_C")) != 0);
      if (reset_is_set) begin
        progress = (reset_was_set === 1'b0);
        ocp_do_check_reset_indication(command);
        address_shadow = 0;
        configuration_shadow = 0;
        alternate_shadow = 0;
        if (ocp_cfg.ocp_get_epn_profile(device) != null)
          ocp_cfg.epn_enabled[device-1] = 0;
        ocp_write_command(ocp_get_mask("DEVCMDSTAT","DRES_C"));
        ocp_initialize_ep0();
      end
      reset_was_set = reset_is_set;
      ocp_read_csr("INTSTAT",interrupts);
      if ((interrupts & ocp_get_mask("INTSTAT","DEV_INT")) != 0)
        ocp_write_csr("INTSTAT",ocp_get_mask("INTSTAT","DEV_INT"));
      if ((interrupts & ocp_get_mask("INTSTAT","EP0OUT")) != 0) begin
        ocp_write_csr("INTSTAT",ocp_get_mask("INTSTAT","EP0OUT"));
        ocp_read_csr("DEVCMDSTAT",command);
        if ((command & ocp_get_mask("DEVCMDSTAT","SETUP")) != 0) ocp_service_setup();
      end
      // A serviced software-owned request or a new reset indication is work.
      // Sticky EP0IN/DEV_INT, NAK interrupts, and hardware-owned OCP traffic
      // must not keep an otherwise idle firmware actor at the fast interval.
      if (progress || serviced != serviced_before) poll_interval = ocp_cfg.service_poll;
      ocp_wait_service_interval(poll_interval,deadline,"OCP_FIRMWARE",
                                "Persistent service exceeded lifecycle bound");
      poll_interval = ocp_get_next_idle_poll(poll_interval);
    end
    if (serviced == 0 || configuration_shadow !== 1)
      `uvm_fatal("OCP_FIRMWARE", "Persistent actor stopped without enumeration")
    completed = 1;
    ocp_cfg.actor_finished[(device == 1) ? 1 : 3] = 1;
  endtask
endclass
