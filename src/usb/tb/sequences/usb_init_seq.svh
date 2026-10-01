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
//   4. Decode and service seven standard requests: GET_DESCRIPTOR, GET_STATUS,
//      SET_ADDRESS, GET_DESCRIPTOR, GET_CONFIGURATION, SET_CONFIGURATION, and
//      GET_CONFIGURATION.
//   5. Require both host-side transfer validation and the final DUT state of
//      the configured device address, configuration 1, and exactly seven
//      serviced SETUP packets.
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

  // Constructs the sequence; body() coordinates DUT and host enumeration.
  function new(string name = "usb_init_seq");
    super.new(name);
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
    interrupt_enable_value = ral_field_value(p_sequencer.reg_model.combo.dev0_csr.INTEN.EP_INT_EN, ep0_out_endpoint.csr_bit_mask() | ep0_in_endpoint.csr_bit_mask()) |
                             ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.INTEN.DEV_INT_EN);
    vbus_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.VBUS_DEBOUNCED);
    `uvm_info("USB_INIT_SEQ", "Initializing DEV0 endpoint list and control registers", UVM_LOW)
    device_address_shadow = 0;
    current_configuration = 0;
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
    write_devcmdstat(command | reset_change_mask);
    initialize_ep0_entries();
    ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    command &= ~dev_addr_mask;
    write_devcmdstat(command);
  endtask

  // Decode the two little-endian words written by hardware into the EP0 SETUP
  // buffer into the standard eight-byte request fields.
  task read_setup_packet(output byte unsigned request_type, output byte unsigned request, output logic [15:0] value, output logic [15:0] index, output logic [15:0] length);
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
  task send_ep0_data(logic [31:0] data_words[5], int unsigned byte_count);
    int unsigned word_count;

    word_count = (byte_count + 3) / 4;
    for (int unsigned word_index = 0; word_index < word_count; word_index++) begin
      write32(USB_DEV0_SRAM, ep0_in_buffer_offset + word_index * 4, data_words[word_index]);
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
  task service_setup_request();
    byte unsigned request_type;
    byte unsigned request;
    logic [15:0] value;
    logic [15:0] index;
    logic [15:0] length;
    logic [31:0] command;
    logic [31:0] ep0in_mask;
    logic [31:0] intonnak_ci_mask;
    logic [31:0] intonnak_co_mask;
    logic [31:0] response_words[5];
    int unsigned response_length;

    ep0in_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.INTSTAT.EP0IN);
    intonnak_ci_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.INTONNAK_CI);
    intonnak_co_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.INTONNAK_CO);
    response_words = '{
      32'h0002_0112,
      32'h4000_0000,
      32'h0000_0000,
      32'h0000_0100,
      32'h0100_0000
    };
    read_setup_packet(request_type, request, value, index, length);
    ral_write32("INTSTAT.EP0IN", p_sequencer.reg_model.combo.dev0_csr.INTSTAT, ep0in_mask);

    case (request)
      8'h06: begin
        // Return at most the fixed 18-byte device descriptor requested by host.
        if (request_type != 8'h80 || value[15:8] != 8'h01) begin
          `uvm_fatal("USB_INIT_SEQ", "Unexpected GET_DESCRIPTOR request")
        end
        response_length = length < 18 ? length : 18;
        send_ep0_data(response_words, response_length);
        arm_ep0_out();
        ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
        // Match the firmware's descriptor status-phase detection policy:
        // enable INTONNAK_CO and clear INTONNAK_CI.
        command |= intonnak_co_mask;
        command &= ~intonnak_ci_mask;
        write_devcmdstat(command);
      end
      8'h00: begin
        // Report the two-byte, all-zero device status expected by
        // this scenario.
        if (request_type != 8'h80 || length != 2) begin
          `uvm_fatal("USB_INIT_SEQ", "Unexpected GET_STATUS request")
        end
        response_words = '{default: 0};
        send_ep0_data(response_words, 2);
        arm_ep0_out();
      end
      8'h05: begin
        // Match firmware ordering: arm status IN and rearm OUT, then program
        // the shadowed address. This branch does not wait for USB completion.
        if (request_type != 8'h00 || length != 0) begin
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
        if (request_type != 8'h80 || length != 1) begin
          `uvm_fatal("USB_INIT_SEQ", "Unexpected GET_CONFIGURATION request")
        end
        response_words = '{default: 0};
        response_words[0] = current_configuration;
        send_ep0_data(response_words, 1);
        arm_ep0_out();
      end
      8'h09: begin
        // Accept only configuration zero or the scenario's configuration one,
        // then acknowledge with a zero-length status packet.
        if (request_type != 8'h00 || length != 0 || value[7:0] > 1) begin
          `uvm_fatal("USB_INIT_SEQ", "Unexpected SET_CONFIGURATION request")
        end
        current_configuration = value[7:0];
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
        "Serviced SETUP %0d/7: type=0x%02h request=0x%02h value=0x%04h index=0x%04h length=%0d",
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

  // Poll reset and interrupt state until all seven SETUP packets are serviced.
  // Device events are acknowledged independently from EP0 OUT events so a
  // reset cannot be hidden by simultaneous control traffic.
  task service_ep0();
    logic [31:0] command;
    logic [31:0] dev_int_mask;
    logic [31:0] ep0out_mask;
    logic [31:0] interrupt_status;
    logic [31:0] setup_mask;

    dev_int_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.INTSTAT.DEV_INT);
    ep0out_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.INTSTAT.EP0OUT);
    setup_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.SETUP);
    `uvm_info("USB_INIT_SEQ", "Starting concurrent bus-reset and EP0 SETUP service", UVM_LOW)
    while (serviced_request_count < 7) begin
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
    `uvm_info("USB_INIT_SEQ", "All seven EP0 SETUP requests were serviced", UVM_LOW)
  endtask

  // Initialize the controller, then run the host's seven transfers and DUT EP0
  // service concurrently. Publish completion only when both sides and the
  // address/configuration shadows agree on the final enumerated state.
  virtual task body();
    usb_init_host_seq host_sequence;

    completed = 1'b0;
    serviced_request_count = 0;
    if (p_sequencer.host_sequencer == null) begin
      `uvm_fatal("USB_INIT_SEQ", "INIT requires the SVT host virtual sequencer")
    end

    `uvm_info("USB_INIT_SEQ", "Starting standalone USB INIT scenario", UVM_LOW)
    ep0_out_endpoint = get_endpoint(0, USB_DIRECTION_OUT);
    ep0_in_endpoint = get_endpoint(0, USB_DIRECTION_IN);
    `uvm_info("USB_INIT_SEQ", $sformatf("Control endpoint resolved: %s / %s", ep0_out_endpoint.convert2string(), ep0_in_endpoint.convert2string()), UVM_LOW)
    check_buffer_clear_of_endpoint_list("EP0 SETUP", setup_buffer_offset, 8);
    check_buffer_clear_of_endpoint_list("EP0 OUT", ep0_out_buffer_offset, ep0_out_endpoint.max_packet_size);
    check_buffer_clear_of_endpoint_list("EP0 IN", ep0_in_buffer_offset, ep0_in_endpoint.max_packet_size);
    initialize_controller();
    host_sequence = usb_init_host_seq::type_id::create("host_sequence");
    host_sequence.control_endpoint = ep0_out_endpoint;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.link_timeout = p_sequencer.cfg.link_timeout;
    host_sequence.control_transfer_timeout = p_sequencer.cfg.control_transfer_timeout;

    // The host blocks on real bus completions while service_ep0 supplies each
    // response through the DUT's CSRs and packet memory.
    fork
      begin
        host_sequence.start(p_sequencer.host_sequencer);
        if (!host_sequence.completed) begin
          `uvm_fatal("USB_INIT_SEQ", "Host sequence returned incomplete")
        end
      end
      begin
        service_ep0();
      end
    join

    completed = host_sequence.completed && serviced_request_count == 7 && current_configuration == 1 && device_address_shadow == p_sequencer.cfg.device_address;
    if (!completed) begin
      `uvm_fatal("USB_INIT_SEQ", $sformatf("INIT final state invalid: host=%0b serviced=%0d address=%0d (expected %0d) configuration=%0d", host_sequence.completed, serviced_request_count, device_address_shadow, p_sequencer.cfg.device_address, current_configuration))
    end
    `uvm_info("USB_INIT_SEQ", "Standalone USB INIT completed with seven real USB transfers", UVM_LOW)
  endtask
endclass
