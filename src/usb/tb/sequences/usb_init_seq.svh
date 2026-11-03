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
//
// Replaces the subsystem USB INIT firmware with UVM frontdoor activity. This
// sequence implements the DUT-facing half of the enumeration scenario:
//
//   1. Initialize EP0 packet-memory entries and DEV0 control/interrupt CSRs.
//   2. Wait for VBUS, enable/connect the controller, and handle the USB reset.
//   3. Run usb_init_host_seq while concurrently polling DEV0 reset and EP0
//      interrupt state.
//   4. Service device/configuration discovery, status, address assignment,
//      configuration selection, and configuration readback.
//   5. Require both host-side transfer validation and the final DUT state of
//      the configured device address, advertised configuration, and every
//      expected SETUP packet.
//
// usb_base_seq provides CSR RAL, native DEV0 packet-SRAM accesses, and the
// generic endpoint-list and per-endpoint interrupt mechanics. Other scenarios
// that need an enumerated device start this sequence as a child. Scenario
// waits and native accesses are bounded, and each unsupported or malformed
// request fails rather than receiving a fallback response.
class usb_init_seq extends usb_base_seq;
  `uvm_object_utils(usb_init_seq)

  // On EP0 OUT, the second entry word is the SETUP buffer descriptor.
  localparam int unsigned SETUP_ENTRY_SELECT = 1;
  localparam byte unsigned CONFIGURATION_VALUE = 1;
  // USB 2.0 chapter 9 standard descriptor types and lengths.
  localparam byte unsigned DEVICE_DESCRIPTOR_TYPE = 1;
  localparam byte unsigned CONFIGURATION_DESCRIPTOR_TYPE = 2;
  localparam byte unsigned INTERFACE_DESCRIPTOR_TYPE = 4;
  localparam byte unsigned ENDPOINT_DESCRIPTOR_TYPE = 5;
  // USB 2.0 LPM ECN section 3, Table 3-1 and the BOS descriptor format.
  localparam byte unsigned BOS_DESCRIPTOR_TYPE = 15;
  localparam byte unsigned DEVICE_CAPABILITY_DESCRIPTOR_TYPE = 16;
  localparam byte unsigned USB20_EXTENSION_CAPABILITY_TYPE = 2;
  localparam byte unsigned USB20_LPM_ATTRIBUTE = 8'h02;
  localparam int unsigned BOS_DESCRIPTOR_LENGTH = 5;
  localparam int unsigned USB20_EXTENSION_DESCRIPTOR_LENGTH = 7;
  localparam int unsigned DEVICE_DESCRIPTOR_LENGTH = 18;
  localparam int unsigned CONFIGURATION_DESCRIPTOR_LENGTH = 9;
  localparam int unsigned INTERFACE_DESCRIPTOR_LENGTH = 9;
  localparam int unsigned ENDPOINT_DESCRIPTOR_LENGTH = 7;
  localparam byte unsigned ISOCHRONOUS_ENDPOINT_TYPE = 1;
  localparam byte unsigned BULK_ENDPOINT_TYPE = 2;
  localparam byte unsigned INTERRUPT_ENDPOINT_TYPE = 3;
  // USB 2.0 sections 9.4.1, 9.4.5 and 9.6.3.
  localparam logic [15:0] DEVICE_REMOTE_WAKEUP_FEATURE = 16'd1;
  localparam byte unsigned REMOTE_WAKEUP_ATTRIBUTE = 8'h20;
  localparam byte unsigned REMOTE_WAKEUP_STATUS = 8'h02;
  byte unsigned device_descriptor[$];
  byte unsigned configuration_descriptor[$];
  byte unsigned bos_descriptor[$];
  bit lpm_supported;
  bit remote_wakeup_supported;
  bit remote_wakeup_enabled;

  // EP0 packet-memory buffers, as byte offsets from DATABUFSTART (0). A
  // parent scenario may move them before start; they must stay clear of the
  // endpoint list and of any buffer the parent uses itself.
  logic [31:0] setup_buffer_offset = 32'h0000_0100;
  logic [31:0] ep0_out_buffer_offset = 32'h0000_0140;
  logic [31:0] ep0_in_buffer_offset = 32'h0000_0180;

  // The USB virtual sequencer supplies the RAL, memory, and SVT access paths.
  bit completed;

  // Both halves of the control endpoint, resolved from the environment
  // configuration at the start of body().
  usb_endpoint_cfg ep0_out_endpoint;
  usb_endpoint_cfg ep0_in_endpoint;

  // Track protocol state independently from the underlying DEV0 CSR fields.
  byte unsigned device_address_shadow;
  byte unsigned current_configuration;
  int unsigned serviced_request_count;
  bit host_scenario_completed;

  // Constructs the sequence; body() coordinates DUT and host enumeration.
  function new(string name = "usb_init_seq");
    super.new(name);
  endfunction

  // Number of SETUP requests the selected enumeration scenario services.
  virtual function int unsigned expected_setup_request_count();
    return usb_init_host_seq::ENUMERATION_REQUEST_COUNT;
  endfunction

  // USB 2.0 sections 9.6.1, 9.6.3, 9.6.5 and 9.6.6. This device fixture
  // exposes one bus-powered, vendor-specific interface containing its endpoints.
  function void build_descriptors();
    int unsigned total_length;

    total_length = CONFIGURATION_DESCRIPTOR_LENGTH + INTERFACE_DESCRIPTOR_LENGTH +
                   ENDPOINT_DESCRIPTOR_LENGTH * p_sequencer.cfg.endpoint_cfgs.size();
    // The shared fixture uses one EP0 packet and a 64-byte IN buffer.
    if (ep0_in_endpoint.max_packet_size != 64 || total_length > 64) begin
      `uvm_fatal("USB_INIT_SEQ", "Descriptor fixture requires HS EP0 and configuration data fitting in 64 bytes")
    end
    device_descriptor = '{
      DEVICE_DESCRIPTOR_LENGTH, DEVICE_DESCRIPTOR_TYPE, lpm_supported ? 8'h01 : 8'h00, 8'h02, 0, 0, 0, 64,
      0, 0, 0, 0, 8'h00, 8'h01, 0, 0, 0, 1
    };
    configuration_descriptor = '{
      CONFIGURATION_DESCRIPTOR_LENGTH, CONFIGURATION_DESCRIPTOR_TYPE,
      8'(total_length), 8'(total_length >> 8), 1, CONFIGURATION_VALUE, 0,
      8'h80 | (remote_wakeup_supported ? REMOTE_WAKEUP_ATTRIBUTE : 8'h00), 50,
      INTERFACE_DESCRIPTOR_LENGTH, INTERFACE_DESCRIPTOR_TYPE,
      0, 0, 8'(p_sequencer.cfg.endpoint_cfgs.size()), 8'hff, 0, 0, 0
    };
    bos_descriptor = '{
      BOS_DESCRIPTOR_LENGTH, BOS_DESCRIPTOR_TYPE,
      8'(BOS_DESCRIPTOR_LENGTH + USB20_EXTENSION_DESCRIPTOR_LENGTH), 8'h00, 8'h01,
      USB20_EXTENSION_DESCRIPTOR_LENGTH, DEVICE_CAPABILITY_DESCRIPTOR_TYPE,
      USB20_EXTENSION_CAPABILITY_TYPE, USB20_LPM_ATTRIBUTE, 8'h00, 8'h00, 8'h00
    };
    foreach (p_sequencer.cfg.endpoint_cfgs[endpoint_index]) begin
      usb_endpoint_cfg endpoint;
      byte unsigned attributes;
      int unsigned packet_size;
      int unsigned additional_transactions;

      endpoint = p_sequencer.cfg.endpoint_cfgs[endpoint_index];
      if (endpoint == null) begin
        `uvm_fatal("USB_INIT_SEQ", "Null endpoint in descriptor fixture")
      end
      additional_transactions = endpoint.isoc_mult_valid ? endpoint.isoc_mult : 0;
      case (endpoint.transfer_type)
        USB_TRANSFER_TYPE_BULK: attributes = BULK_ENDPOINT_TYPE;
        USB_TRANSFER_TYPE_INTERRUPT: attributes = INTERRUPT_ENDPOINT_TYPE;
        USB_TRANSFER_TYPE_ISOCHRONOUS: attributes = ISOCHRONOUS_ENDPOINT_TYPE;
        default: `uvm_fatal("USB_INIT_SEQ", "Only non-control endpoints belong in the interface descriptor")
      endcase
      if (endpoint.ep_number == 0 || endpoint.ep_number > 15 ||
          endpoint.max_packet_size == 0 || endpoint.max_packet_size > 1024 ||
          additional_transactions > 2 || endpoint.interval > 255 ||
          (attributes == BULK_ENDPOINT_TYPE && (endpoint.max_packet_size != 512 || additional_transactions != 0)) ||
          (attributes != BULK_ENDPOINT_TYPE && (endpoint.interval == 0 || endpoint.interval > 16))) begin
        `uvm_fatal("USB_INIT_SEQ", $sformatf("Invalid HS descriptor endpoint: %s", endpoint.convert2string()))
      end
      // isoc_mult represents wMaxPacketSize[12:11] in USB 2.0; max_burst_size
      // belongs to the USB 3.0 companion descriptor and is not encoded here.
      packet_size = endpoint.max_packet_size | (additional_transactions << 11);
      configuration_descriptor.push_back(ENDPOINT_DESCRIPTOR_LENGTH);
      configuration_descriptor.push_back(ENDPOINT_DESCRIPTOR_TYPE);
      configuration_descriptor.push_back(8'(endpoint.ep_number) |
                                         (endpoint.direction == USB_DIRECTION_IN ? 8'h80 : 8'h00));
      configuration_descriptor.push_back(attributes);
      configuration_descriptor.push_back(8'(packet_size));
      configuration_descriptor.push_back(8'(packet_size >> 8));
      configuration_descriptor.push_back(8'(endpoint.interval));
    end
  endfunction

  // Preserve the protocol-owned address shadow whenever DEVCMDSTAT is written.
  task write_devcmdstat(logic [31:0] value);
    uvm_reg_field dev_addr_field;
    logic [31:0] dev_addr_mask;

    dev_addr_field = p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.DEV_ADDR;
    dev_addr_mask = ral_field_mask(dev_addr_field);
    value = (value & ~dev_addr_mask) | ral_field_value(dev_addr_field, device_address_shadow);
    ral_write32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, value);
  endtask

  // Arm EP0 OUT for the next SETUP packet and clear both control-transfer
  // descriptor words used for OUT status and IN data stages.
  task initialize_ep0_entries();
    write_endpoint_entry(ep0_out_endpoint, endpoint_entry(1'b1, 1'b0, 8, ep0_out_buffer_offset));
    write_endpoint_entry(ep0_out_endpoint, endpoint_entry(1'b0, 1'b0, 0, setup_buffer_offset), SETUP_ENTRY_SELECT);
    write_endpoint_entry(ep0_in_endpoint, endpoint_entry(1'b0, 1'b0, 0, ep0_in_buffer_offset));
  endtask

  // Prepare packet memory and DEV0 CSRs, wait for VBUS, then enable/connect the
  // controller and arm the device, EP0 OUT, and EP0 IN interrupts.
  task initialize_controller();
    logic [31:0] command;
    logic [31:0] enable_connect_value;
    logic [31:0] interrupt_enable_value;
    logic [31:0] vbus_mask;
    bit vbus_detected;

    enable_connect_value = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.DEV_EN) |
                           ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.DCON);
    // Keep hardware LPM acceptance consistent with the advertised capability.
    if (lpm_supported) enable_connect_value |= ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.LPM_SUP);
    interrupt_enable_value = ral_field_value(
                               p_sequencer.reg_model.combo.dev0_csr.INTEN.EP_INT_EN,
                               ep0_out_endpoint.csr_bit_mask() | ep0_in_endpoint.csr_bit_mask()
                             ) |
                             ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.INTEN.DEV_INT_EN);
    vbus_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.VBUS_DEBOUNCED);
    `uvm_info("USB_INIT_SEQ", "Initializing DEV0 endpoint list and control registers", UVM_LOW)
    device_address_shadow = 0;
    current_configuration = 0;
    remote_wakeup_enabled = 1'b0;
    initialize_ep0_entries();
    // Clear every non-EP0 entry so no endpoint starts active.
    write32(USB_DEV0_SRAM, endpoint_list_base() + 32'h00c, 0);
    for (logic [31:0] offset = 32'h010; offset < p_sequencer.cfg.endpoint_list_bytes(); offset += 4) begin
      write32(USB_DEV0_SRAM, endpoint_list_base() + offset, 0);
    end

    ral_write32("EPLISTSTART", p_sequencer.reg_model.combo.dev0_csr.EPLISTSTART, endpoint_list_base());
    ral_write32("DATABUFSTART", p_sequencer.reg_model.combo.dev0_csr.DATABUFSTART, 0);

    vbus_detected = 1'b0;
    `uvm_info("USB_INIT_SEQ", "Waiting for VBUS_DEBOUNCED", UVM_LOW)
    fork
      begin
        do begin
          ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
          if (!(command & vbus_mask)) begin
            #100ns;
          end
        end while (!(command & vbus_mask));
        vbus_detected = 1'b1;
      end
      begin
        #(p_sequencer.cfg.vbus_timeout);
      end
    join_any
    disable fork;
    if (!vbus_detected) begin
      `uvm_fatal("USB_INIT_SEQ", $sformatf("VBUS was not detected within %0t", p_sequencer.cfg.vbus_timeout))
    end

    `uvm_info("USB_INIT_SEQ", "VBUS detected; allowing the remote PHY to settle before DEV_EN/DCON", UVM_LOW)
    #20us;
    write_devcmdstat(enable_connect_value);
    ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    if ((command & enable_connect_value) != enable_connect_value) begin
      `uvm_fatal("USB_INIT_SEQ", $sformatf("Device did not enable/connect; DEVCMDSTAT=0x%08h", command))
    end
    ral_write32("INTEN", p_sequencer.reg_model.combo.dev0_csr.INTEN, interrupt_enable_value);
    ral_write32("INTSTAT", p_sequencer.reg_model.combo.dev0_csr.INTSTAT, USB_DEV0_ROUTE_MASK);
    `uvm_info("USB_INIT_SEQ", "DEV0 initialized, connected, and ready for USB reset", UVM_LOW)
  endtask

  // Acknowledge a detected USB reset, restore address/configuration protocol
  // state, and rearm EP0 before the next SETUP packet.
  task handle_bus_reset(logic [31:0] command);
    logic [31:0] dev_addr_mask;
    logic [31:0] reset_change_mask;

    dev_addr_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.DEV_ADDR);
    reset_change_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.DRES_C);
    if (!(command & reset_change_mask)) begin
      return;
    end
    `uvm_info("USB_INIT_SEQ", "Handling USB bus reset", UVM_LOW)
    device_address_shadow = 0;
    current_configuration = 0;
    remote_wakeup_enabled = 1'b0;
    write_devcmdstat(command | reset_change_mask);
    initialize_ep0_entries();
    ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    command &= ~dev_addr_mask;
    write_devcmdstat(command);
  endtask

  // Decode the two little-endian words written by hardware into the EP0 SETUP
  // buffer into the standard eight-byte request fields.
  task read_setup_packet(
    output byte unsigned request_type,
    output byte unsigned request,
    output logic [15:0] value,
    output logic [15:0] index,
    output logic [15:0] length
  );
    logic [31:0] word0;
    logic [31:0] word1;

    read32(USB_DEV0_SRAM, setup_buffer_offset, word0);
    read32(USB_DEV0_SRAM, setup_buffer_offset + 4, word1);
    request_type = word0[7:0];
    request = word0[15:8];
    value = word0[31:16];
    index = word1[15:0];
    length = word1[31:16];
  endtask

  // Populate the EP0 IN buffer and transfer ownership to hardware for a
  // bounded data-stage response.
  task send_ep0_data(byte unsigned data_bytes[$], int unsigned byte_count);
    logic [31:0] word;

    if (byte_count == 0 || byte_count > data_bytes.size() || byte_count > ep0_in_endpoint.max_packet_size) begin
      `uvm_fatal("USB_INIT_SEQ", "Invalid EP0 data response length")
    end
    for (int unsigned byte_index = 0; byte_index < byte_count; byte_index += 4) begin
      word = 0;
      for (int unsigned lane = 0; lane < 4 && byte_index + lane < byte_count; lane++) begin
        word[lane * 8 +: 8] = data_bytes[byte_index + lane];
      end
      write_sram_bytes(USB_DEV0_SRAM, ep0_in_buffer_offset + byte_index, word, byte_count - byte_index);
    end
    write_endpoint_entry(ep0_in_endpoint, endpoint_entry(1'b1, 1'b0, byte_count, ep0_in_buffer_offset));
  endtask

  // Arm a zero-length EP0 IN packet for a no-data request, without waiting for
  // USB completion; the host sequence validates that completion separately.
  task send_ep0_zlp();
    write_endpoint_entry(ep0_in_endpoint, endpoint_entry(1'b1, 1'b0, 0, ep0_in_buffer_offset));
  endtask

  // Return EP0 OUT ownership to hardware for the next status or SETUP packet.
  task arm_ep0_out();
    write_endpoint_entry(ep0_out_endpoint, endpoint_entry(1'b1, 1'b0, 0, ep0_out_buffer_offset));
  endtask

  // Acknowledge the SETUP latch while preserving the shadowed device address.
  task clear_setup_bit();
    logic [31:0] command;
    logic [31:0] setup_mask;

    setup_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.SETUP);
    ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    write_devcmdstat(command | setup_mask);
  endtask

  // Validate and service one latched standard device request. Each supported
  // request prepares its data/status stage, rearms EP0 as needed, updates the
  // protocol shadow state, and contributes exactly one completion count.
  virtual task service_setup_request();
    byte unsigned request_type;
    byte unsigned request;
    logic [15:0] value;
    logic [15:0] index;
    logic [15:0] length;
    logic [31:0] command;
    logic [31:0] ep0in_mask;
    logic [31:0] intonnak_ci_mask;
    logic [31:0] intonnak_co_mask;
    byte unsigned response_bytes[$];
    int unsigned response_length;

    ep0in_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.INTSTAT.EP0IN);
    intonnak_ci_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.INTONNAK_CI);
    intonnak_co_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.INTONNAK_CO);
    read_setup_packet(request_type, request, value, index, length);
    ral_write32("INTSTAT.EP0IN", p_sequencer.reg_model.combo.dev0_csr.INTSTAT, ep0in_mask);

    case (request)
      8'h06: begin
        if (request_type != 8'h80 || value[7:0] != 0 || index != 0 || length == 0) begin
          `uvm_fatal("USB_INIT_SEQ", "Unexpected GET_DESCRIPTOR request")
        end
        case (value[15:8])
          DEVICE_DESCRIPTOR_TYPE: response_bytes = device_descriptor;
          CONFIGURATION_DESCRIPTOR_TYPE: response_bytes = configuration_descriptor;
          BOS_DESCRIPTOR_TYPE: begin
            if (!lpm_supported) begin
              `uvm_fatal("USB_INIT_SEQ", "BOS was requested from a fixture without LPM capability")
            end
            response_bytes = bos_descriptor;
          end
          default: `uvm_fatal("USB_INIT_SEQ", "Unsupported descriptor type")
        endcase
        response_length = length < response_bytes.size() ? length : response_bytes.size();
        send_ep0_data(response_bytes, response_length);
        arm_ep0_out();
        ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
        // Match the firmware's descriptor status-phase detection policy:
        // enable INTONNAK_CO and clear INTONNAK_CI.
        command |= intonnak_co_mask;
        command &= ~intonnak_ci_mask;
        write_devcmdstat(command);
      end
      8'h00: begin
        if (request_type != 8'h80 || value != 0 || index != 0 || length != 2) begin
          `uvm_fatal("USB_INIT_SEQ", "Unexpected GET_STATUS request")
        end
        response_bytes = '{remote_wakeup_enabled ? REMOTE_WAKEUP_STATUS : 8'h00, 8'h00};
        send_ep0_data(response_bytes, 2);
        arm_ep0_out();
      end
      8'h05: begin
        // Match firmware ordering: arm status IN and rearm OUT, then program
        // the shadowed address. This branch does not wait for USB completion.
        if (request_type != 8'h00 || value > 127 || index != 0 || length != 0) begin
          `uvm_fatal("USB_INIT_SEQ", "Unexpected SET_ADDRESS request")
        end
        send_ep0_zlp();
        arm_ep0_out();
        device_address_shadow = value[6:0];
        ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
        write_devcmdstat(command);
      end
      8'h08: begin
        // Return the current configuration shadow before or after selection.
        if (request_type != 8'h80 || value != 0 || index != 0 || length != 1) begin
          `uvm_fatal("USB_INIT_SEQ", "Unexpected GET_CONFIGURATION request")
        end
        response_bytes = '{current_configuration};
        send_ep0_data(response_bytes, 1);
        arm_ep0_out();
      end
      8'h09: begin
        // Accept only configuration zero or the advertised configuration,
        // then acknowledge with a zero-length status packet.
        if (request_type != 8'h00 || length != 0 || index != 0 ||
            (value != 0 && value != CONFIGURATION_VALUE)) begin
          `uvm_fatal("USB_INIT_SEQ", "Unexpected SET_CONFIGURATION request")
        end
        current_configuration = value[7:0];
        remote_wakeup_enabled = 1'b0;
        send_ep0_zlp();
        arm_ep0_out();
      end
      8'h01, 8'h03: begin
        if (!remote_wakeup_supported || current_configuration == 0 ||
            request_type != 8'h00 || value != DEVICE_REMOTE_WAKEUP_FEATURE ||
            index != 0 || length != 0) begin
          `uvm_fatal("USB_INIT_SEQ", "Unexpected device feature request")
        end
        remote_wakeup_enabled = request == 8'h03;
        send_ep0_zlp();
        arm_ep0_out();
      end
      default: begin
        // Stall both directions before rejecting an unsupported request.
        write_endpoint_entry(ep0_in_endpoint, endpoint_entry(1'b0, 1'b1, 0, ep0_in_buffer_offset));
        write_endpoint_entry(ep0_out_endpoint, endpoint_entry(1'b0, 1'b1, 0, ep0_out_buffer_offset));
        `uvm_fatal("USB_INIT_SEQ", $sformatf("Unsupported control request 0x%02h", request))
      end
    endcase

    clear_setup_bit();
    serviced_request_count++;
    `uvm_info(
      "USB_INIT_SEQ",
      $sformatf(
        "Serviced SETUP %0d: type=0x%02h request=0x%02h value=0x%04h index=0x%04h length=%0d",
        serviced_request_count,
        request_type,
        request,
        value,
        index,
        length
      ),
      UVM_LOW
    )
  endtask

  // Poll reset and interrupt state until every expected SETUP packet is serviced.
  // Device events are acknowledged independently from EP0 OUT events so a
  // reset cannot be hidden by simultaneous control traffic.
  task service_ep0(int unsigned request_count = expected_setup_request_count());
    logic [31:0] command;
    logic [31:0] dev_int_mask;
    logic [31:0] ep0out_mask;
    logic [31:0] interrupt_status;
    logic [31:0] setup_mask;

    dev_int_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.INTSTAT.DEV_INT);
    ep0out_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.INTSTAT.EP0OUT);
    setup_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.SETUP);
    `uvm_info("USB_INIT_SEQ", "Starting concurrent bus-reset and EP0 SETUP service", UVM_LOW)
    while (serviced_request_count < request_count) begin
      ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
      handle_bus_reset(command);
      ral_read32("INTSTAT", p_sequencer.reg_model.combo.dev0_csr.INTSTAT, interrupt_status);

      if (interrupt_status & dev_int_mask) begin
        ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
        handle_bus_reset(command);
        ral_write32("INTSTAT.DEV_INT", p_sequencer.reg_model.combo.dev0_csr.INTSTAT, dev_int_mask);
        `uvm_info("USB_INIT_SEQ", "Cleared DEV_INT after device-event handling", UVM_LOW)
      end

      if (interrupt_status & ep0out_mask) begin
        ral_write32("INTSTAT.EP0OUT", p_sequencer.reg_model.combo.dev0_csr.INTSTAT, ep0out_mask);
        ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
        if (command & setup_mask) begin
          service_setup_request();
        end
      end else begin
        #50ns;
      end
    end
    `uvm_info(
      "USB_INIT_SEQ",
      $sformatf("All %0d EP0 SETUP requests were serviced", request_count),
      UVM_LOW
    )
  endtask

  // Run the host side of the enumeration flow.
  virtual task run_host_scenario();
    usb_init_host_seq host_sequence;

    host_scenario_completed = 1'b0;
    host_sequence = usb_init_host_seq::type_id::create("host_sequence");
    host_sequence.control_endpoint = ep0_out_endpoint;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.link_timeout = p_sequencer.cfg.link_timeout;
    host_sequence.control_transfer_timeout = p_sequencer.cfg.control_transfer_timeout;
    host_sequence.start(p_sequencer.host_sequencer);
    if (!host_sequence.completed) begin
      `uvm_fatal("USB_INIT_SEQ", "Host sequence returned incomplete")
    end
    host_scenario_completed = 1'b1;
  endtask

  // Initialize the controller, then run the host's transfers and DUT EP0
  // service concurrently. Publish completion only when both sides and the
  // address/configuration shadows agree on the final enumerated state.
  virtual task body();
    completed = 1'b0;
    host_scenario_completed = 1'b0;
    serviced_request_count = 0;
    if (p_sequencer.host_sequencer == null) begin
      `uvm_fatal("USB_INIT_SEQ", "INIT requires the SVT host virtual sequencer")
    end

    `uvm_info("USB_INIT_SEQ", "Starting standalone USB INIT scenario", UVM_LOW)
    ep0_out_endpoint = get_endpoint(0, USB_DIRECTION_OUT);
    ep0_in_endpoint = get_endpoint(0, USB_DIRECTION_IN);
    build_descriptors();
    `uvm_info("USB_INIT_SEQ", $sformatf("Control endpoint resolved: %s / %s", ep0_out_endpoint.convert2string(), ep0_in_endpoint.convert2string()), UVM_LOW)
    check_buffer_clear_of_endpoint_list("EP0 SETUP", setup_buffer_offset, 8);
    check_buffer_clear_of_endpoint_list("EP0 OUT", ep0_out_buffer_offset, ep0_out_endpoint.max_packet_size);
    check_buffer_clear_of_endpoint_list("EP0 IN", ep0_in_buffer_offset, ep0_in_endpoint.max_packet_size);
    initialize_controller();

    // The host blocks on real bus completions while service_ep0 supplies each
    // response through the DUT's CSRs and packet memory.
    fork
      begin
        run_host_scenario();
      end
      begin
        service_ep0();
      end
    join

    completed = host_scenario_completed &&
                serviced_request_count == expected_setup_request_count() &&
                current_configuration == CONFIGURATION_VALUE &&
                device_address_shadow == p_sequencer.cfg.device_address;
    if (!completed) begin
      `uvm_fatal(
        "USB_INIT_SEQ",
        $sformatf(
          "INIT final state invalid: host=%0b serviced=%0d expected=%0d address=%0d (expected %0d) configuration=%0d",
          host_scenario_completed,
          serviced_request_count,
          expected_setup_request_count(),
          device_address_shadow,
          p_sequencer.cfg.device_address,
          current_configuration
        )
      )
    end
    `uvm_info("USB_INIT_SEQ", $sformatf("USB control scenario completed with %0d real transfers", expected_setup_request_count()), UVM_LOW)
  endtask
endclass
