// SPDX-License-Identifier: Apache-2.0

// Generalizes origin/willoneill-usb-bulk-ping's double-buffer scenario.
// Native bulk transfers retain toggles, completion/ZLP policy and IN checking;
// shared packet-memory utilities check both descriptor and byte ownership.
class usb_double_buffer_bulk_seq extends usb_packet_buffer_seq;
  `uvm_object_utils(usb_double_buffer_bulk_seq)

  time transfer_timeout = 500us;
  logic [7:0] packet_tag_stride = 8'h31;
  bit completed;

  // Construct the reusable speed-independent scenario.
  function new(string name = "usb_double_buffer_bulk_seq");
    super.new(name);
  endfunction

  // Service both buffers, preserving the existing full-packet IN ZLP scenario.
  task exchange_pair(usb_endpoint_cfg endpoint, int unsigned second_bytes);
    usb_bulk_out_host_seq out_host;
    usb_bulk_in_host_seq in_host;
    usb_ep_entry_t entries[2];
    usb_ep_entry_t zlp;
    logic [31:0] addresses[2];
    logic [7:0] bases[2];
    int unsigned lengths[2];
    int unsigned mps;
    bit in_direction;
    bit aligned;

    mps = endpoint.max_packet_size;
    lengths[0] = mps;
    lengths[1] = second_bytes;
    in_direction = endpoint.direction == USB_DIRECTION_IN;
    aligned = second_bytes == mps;
    addresses[0] = in_direction ? 32'h1800 : 32'h1000;
    addresses[1] = addresses[0] + 32'h400;
    bases[0] = in_direction ? 8'h80 : 8'h20;
    bases[1] = bases[0] + mps + packet_tag_stride;
    `uvm_info("USB_DOUBLE_BUFFER", $sformatf("Starting %s double-buffer pair: lengths=%0d/%0d", endpoint.short_name(), mps, second_bytes), UVM_LOW)
    clear_endpoint_interrupt(endpoint);
    // Both previous entries have retired before selecting buffer zero again.
    ral_write32("EPINUSE", p_sequencer.reg_model.combo.dev0_csr.EPINUSE, 32'h0);
    foreach (entries[index]) begin
      prepare_packet_buffer(addresses[index], mps, lengths[index], bases[index], in_direction);
      // Short OUT must retire with unused capacity, not merely exhaust NBytes.
      arm_endpoint(endpoint, in_direction ? lengths[index] : mps, addresses[index], entries[index], index);
    end
    if (!in_direction) begin
      out_host = usb_bulk_out_host_seq::type_id::create("out_host");
      out_host.target_endpoint = endpoint;
      out_host.payload_byte_count = mps + second_bytes;
      out_host.payload_base = bases[0];
      out_host.payload_packet_bytes = mps;
      out_host.payload_packet_stride = packet_tag_stride;
      out_host.device_address = p_sequencer.cfg.device_address;
      out_host.bulk_transfer_timeout = transfer_timeout;
      out_host.transfer_label = "Double-buffer bulk OUT";
      out_host.start(p_sequencer.host_sequencer);
      if (!out_host.completed) `uvm_fatal("USB_DOUBLE_BUFFER", "Native bulk OUT incomplete")
    end else begin
      in_host = usb_bulk_in_host_seq::type_id::create("in_host");
      in_host.target_endpoint = endpoint;
      in_host.payload_byte_count = mps + second_bytes;
      in_host.payload_base = bases[0];
      in_host.payload_packet_bytes = mps;
      in_host.payload_packet_stride = packet_tag_stride;
      in_host.device_address = p_sequencer.cfg.device_address;
      in_host.bulk_transfer_timeout = transfer_timeout;
      in_host.transfer_label = "Double-buffer bulk IN";
      in_host.expect_zero_length_termination = aligned;
      fork
        in_host.start(p_sequencer.host_sequencer);
        begin
          foreach (entries[index]) check_packet_retired(endpoint, entries[index], lengths[index], transfer_timeout, "Bulk IN data", index);
          if (aligned) begin
            clear_endpoint_interrupt(endpoint);
            arm_endpoint(endpoint, 0, addresses[0], zlp);
            `uvm_info("USB_DOUBLE_BUFFER", "Both IN data buffers retired; buffer zero rearmed for native terminating ZLP", UVM_LOW)
          end
        end
      join
      if (!in_host.completed) `uvm_fatal("USB_DOUBLE_BUFFER", "Native bulk IN incomplete")
    end
    wait_for_endpoint_interrupt(endpoint, transfer_timeout);
    foreach (entries[index]) begin
      if (in_direction && aligned && index == 0) begin
        check_packet_retired(endpoint, zlp, 0, transfer_timeout, "Bulk IN ZLP");
      end else begin
        check_packet_retired(endpoint, entries[index], lengths[index], transfer_timeout, "Bulk data", index);
      end
      check_packet_buffer(addresses[index], mps, lengths[index], bases[index], in_direction, "Double-buffer payload");
    end
    `uvm_info("USB_DOUBLE_BUFFER", $sformatf("%s double-buffer pair verified: lengths=%0d/%0d", endpoint.short_name(), mps, second_bytes), UVM_LOW)
  endtask

  // Enumerate once, enable double buffering, then exchange full and FS odd data.
  virtual task body();
    usb_init_seq init_sequence;
    usb_endpoint_cfg in_endpoint;
    usb_endpoint_cfg out_endpoint;

    completed = 1'b0;
    if (p_sequencer.cfg.speed == USB_SPEED_FULL) begin
      if (transfer_timeout < USB_FS_BULK_PAIR_TIMEOUT) transfer_timeout = USB_FS_BULK_PAIR_TIMEOUT;
      `uvm_info("USB_DOUBLE_BUFFER", $sformatf("FS native transfer/retirement bound=%0t", transfer_timeout), UVM_LOW)
    end
    `uvm_info("USB_DOUBLE_BUFFER", "Starting double-buffer bulk scenario; enumerating first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) `uvm_fatal("USB_DOUBLE_BUFFER", "Enumeration incomplete")
    in_endpoint = get_endpoint(1, USB_DIRECTION_IN);
    out_endpoint = get_endpoint(1, USB_DIRECTION_OUT);
    if (in_endpoint.transfer_type != USB_TRANSFER_TYPE_BULK || out_endpoint.transfer_type != USB_TRANSFER_TYPE_BULK) begin
      `uvm_fatal("USB_DOUBLE_BUFFER", "EP1 IN/OUT must be bulk")
    end
    ral_write32("EPBUFCFG", p_sequencer.reg_model.combo.dev0_csr.EPBUFCFG, in_endpoint.csr_bit_mask() | out_endpoint.csr_bit_mask());
    enable_endpoint_interrupt(in_endpoint);
    enable_endpoint_interrupt(out_endpoint);
    exchange_pair(out_endpoint, out_endpoint.max_packet_size);
    exchange_pair(in_endpoint, in_endpoint.max_packet_size);
    if (p_sequencer.cfg.speed == USB_SPEED_FULL) begin
      exchange_pair(out_endpoint, 13);
      exchange_pair(in_endpoint, 13);
    end
    completed = 1'b1;
    `uvm_info("USB_DOUBLE_BUFFER", "Both double-buffer directions verified; all entries, bytes and guards checked", UVM_LOW)
  endtask
endclass
