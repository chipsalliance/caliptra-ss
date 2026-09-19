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
//      address 1, configuration 1, and exactly seven serviced SETUP packets.
//
// usb_base_seq provides CSR RAL and native DEV0 packet-SRAM accesses.
// Scenario waits and native accesses are bounded, and each
// unsupported or malformed request fails rather than receiving a fallback
// response.
class usb_init_seq extends usb_base_seq;
  `uvm_object_utils(usb_init_seq)

  localparam logic [31:0] EP_ENTRY_ACTIVE = 32'h8000_0000;
  localparam logic [31:0] EP_ENTRY_STALL = 32'h2000_0000;
  localparam logic [31:0] EP_LIST_OFFSET = 32'h0000_0000;
  localparam logic [31:0] SETUP_BUFFER_OFFSET = 32'h0000_0100;
  localparam logic [31:0] EP0_OUT_BUFFER_OFFSET = 32'h0000_0140;
  localparam logic [31:0] EP0_IN_BUFFER_OFFSET = 32'h0000_0180;
  localparam time VBUS_TIMEOUT = 500us;

  // The USB virtual sequencer supplies the RAL, memory, and SVT access paths.
  bit completed;

  // Track protocol state independently from the underlying DEV0 CSR fields.
  byte unsigned device_address_shadow;
  byte unsigned current_configuration;
  int unsigned serviced_request_count;

  // Constructs the sequence; body() coordinates DUT and host enumeration.
  function new(string name = "usb_init_seq");
    super.new(name);
  endfunction

  // Derive register geometry from generated RAL instead of duplicating masks.
  protected function logic [31:0] ral_field_mask(uvm_reg_field field_handle);
    uvm_reg_data_t mask;

    if (field_handle == null) begin
      `uvm_fatal("USB_INIT_RAL", "Cannot derive a mask from a null RAL field")
    end
    mask = '1;
    mask >>= $bits(mask) - field_handle.get_n_bits();
    mask <<= field_handle.get_lsb_pos();
    return mask[31:0];
  endfunction

  protected function logic [31:0] ral_field_value(uvm_reg_field field_handle, uvm_reg_data_t value);
    uvm_reg_data_t encoded_value;
    logic [31:0] field_mask;

    field_mask = ral_field_mask(field_handle);
    encoded_value = (value << field_handle.get_lsb_pos()) & field_mask;
    return encoded_value[31:0];
  endfunction

  // Encode one DEV0 endpoint-list word from ownership, stall, byte-count, and
  // 64-byte-aligned packet-buffer fields.
  function logic [31:0] endpoint_entry(bit active, bit stall, int unsigned byte_count, logic [31:0] buffer_offset);
    return
      (active ? EP_ENTRY_ACTIVE : 32'h0) |
      (stall ? EP_ENTRY_STALL : 32'h0) |
      ((byte_count & 32'h7fff) << 11) |
      ((buffer_offset >> 6) & 32'h7ff);
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
    write32(USB_DEV0_SRAM, EP_LIST_OFFSET + 32'h000, endpoint_entry(1'b1, 1'b0, 8, EP0_OUT_BUFFER_OFFSET));
    write32(USB_DEV0_SRAM, EP_LIST_OFFSET + 32'h004, endpoint_entry(1'b0, 1'b0, 0, SETUP_BUFFER_OFFSET));
    write32(USB_DEV0_SRAM, EP_LIST_OFFSET + 32'h008, endpoint_entry(1'b0, 1'b0, 0, EP0_IN_BUFFER_OFFSET));
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
    interrupt_enable_value = ral_field_value(p_sequencer.reg_model.combo.dev0_csr.INTEN.EP_INT_EN, 16'h0003) |
                             ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.INTEN.DEV_INT_EN);
    vbus_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.VBUS_DEBOUNCED);
    `uvm_info("USB_INIT_SEQ", "Initializing DEV0 endpoint list and control registers", UVM_LOW)
    device_address_shadow = 0;
    current_configuration = 0;
    initialize_ep0_entries();
    write32(USB_DEV0_SRAM, EP_LIST_OFFSET + 32'h00c, 0);
    for (logic [31:0] offset = 32'h010; offset < SETUP_BUFFER_OFFSET; offset += 4) begin
      write32(USB_DEV0_SRAM, EP_LIST_OFFSET + offset, 0);
    end

    ral_write32("EPLISTSTART", p_sequencer.reg_model.combo.dev0_csr.EPLISTSTART, 0);
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
        #(VBUS_TIMEOUT);
      end
    join_any
    disable fork;
    if (!vbus_detected) begin
      `uvm_fatal("USB_INIT_SEQ", $sformatf("VBUS was not detected within %0t", VBUS_TIMEOUT))
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

    read32(USB_DEV0_SRAM, SETUP_BUFFER_OFFSET, word0);
    read32(USB_DEV0_SRAM, SETUP_BUFFER_OFFSET + 4, word1);
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
      write32(USB_DEV0_SRAM, EP0_IN_BUFFER_OFFSET + word_index * 4, data_words[word_index]);
    end
    write32(USB_DEV0_SRAM, EP_LIST_OFFSET + 32'h008, endpoint_entry(1'b1, 1'b0, byte_count, EP0_IN_BUFFER_OFFSET));
  endtask

  // Arm a zero-length EP0 IN packet for a no-data request, without waiting for
  // USB completion; the host sequence validates that completion separately.
  task send_ep0_zlp();
    write32(USB_DEV0_SRAM, EP_LIST_OFFSET + 32'h008, endpoint_entry(1'b1, 1'b0, 0, EP0_IN_BUFFER_OFFSET));
  endtask

  // Return EP0 OUT ownership to hardware for the next status or SETUP packet.
  task arm_ep0_out();
    write32(USB_DEV0_SRAM, EP_LIST_OFFSET + 32'h000, endpoint_entry(1'b1, 1'b0, 0, EP0_OUT_BUFFER_OFFSET));
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
        // Report the two-byte, all-zero device status expected by this scenario.
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
        write32(USB_DEV0_SRAM, EP_LIST_OFFSET + 32'h008, endpoint_entry(1'b0, 1'b1, 0, EP0_IN_BUFFER_OFFSET));
        write32(USB_DEV0_SRAM, EP_LIST_OFFSET + 32'h000, endpoint_entry(1'b0, 1'b1, 0, EP0_OUT_BUFFER_OFFSET));
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
    initialize_controller();
    host_sequence = usb_init_host_seq::type_id::create("host_sequence");

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

    completed = host_sequence.completed && serviced_request_count == 7 && current_configuration == 1 && device_address_shadow == 1;
    if (!completed) begin
      `uvm_fatal("USB_INIT_SEQ", $sformatf("INIT final state invalid: host=%0b serviced=%0d address=%0d configuration=%0d", host_sequence.completed, serviced_request_count, device_address_shadow, current_configuration))
    end
    `uvm_info("USB_INIT_SEQ", "Standalone USB INIT completed with seven real USB transfers", UVM_LOW)
  endtask
endclass
