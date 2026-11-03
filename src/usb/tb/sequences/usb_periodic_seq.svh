// SPDX-License-Identifier: Apache-2.0

// Ordinary periodic service in both directions. Reuses EP0 enumeration,
// the native periodic host helper and shared packet-memory ownership checks.
// Deliberately excludes HS high-bandwidth partial/aborted interval semantics.
class usb_periodic_seq extends usb_packet_buffer_seq;
  `uvm_object_utils(usb_periodic_seq)

  int unsigned short_bytes = 13;
  time transfer_timeout = USB_FS_PERIODIC_TRANSFER_TIMEOUT;
  bit completed;

  // Construct the reusable periodic scenario.
  function new(string name = "usb_periodic_seq");
    super.new(name);
  endfunction

  // Prepare one buffer and run one native transaction in a separate frame.
  task service_packet(usb_endpoint_cfg endpoint, int unsigned bytes, logic [7:0] base);
    usb_periodic_host_seq host_sequence;
    usb_ep_entry_t armed;
    logic [31:0] address;

    address = endpoint.direction == USB_DIRECTION_IN ? 32'h2000 : 32'h1000;
    prepare_packet_buffer(address, endpoint.max_packet_size, bytes, base, endpoint.direction == USB_DIRECTION_IN);
    clear_endpoint_interrupt(endpoint);
    // Keep OUT capacity above a short payload so residual ownership is checked.
    arm_endpoint(endpoint, endpoint.direction == USB_DIRECTION_OUT ? endpoint.max_packet_size : bytes, address, armed);
    host_sequence = usb_periodic_host_seq::type_id::create("host_sequence");
    host_sequence.target_endpoint = endpoint;
    host_sequence.speed = p_sequencer.cfg.speed;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.payload_byte_count = bytes;
    host_sequence.payload_base = base;
    host_sequence.transfer_timeout = transfer_timeout;
    host_sequence.transfer_label = $sformatf("%s %s bytes=%0d", endpoint.transfer_type.name(), endpoint.short_name(), bytes);
    host_sequence.start(p_sequencer.host_sequencer);
    if (!host_sequence.completed) `uvm_fatal("USB_PERIODIC", "Native periodic transfer incomplete")
    wait_for_endpoint_interrupt(endpoint, transfer_timeout);
    check_packet_retired(endpoint, armed, bytes, transfer_timeout, "Periodic packet");
    check_packet_buffer(address, endpoint.max_packet_size, bytes, base, endpoint.direction == USB_DIRECTION_IN, "Periodic packet");
  endtask

  // Enumerate, then cover full and odd short packets in each direction.
  virtual task body();
    usb_init_seq init_sequence;
    usb_endpoint_cfg in_endpoint;
    usb_endpoint_cfg out_endpoint;

    completed = 1'b0;
    `uvm_info("USB_PERIODIC", "Starting ordinary periodic scenario; running shared enumeration", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) `uvm_fatal("USB_PERIODIC", "Enumeration incomplete")
    in_endpoint = get_endpoint(1, USB_DIRECTION_IN);
    out_endpoint = get_endpoint(1, USB_DIRECTION_OUT);
    if (p_sequencer.cfg.speed != USB_SPEED_FULL ||
        !(in_endpoint.transfer_type inside {USB_TRANSFER_TYPE_INTERRUPT, USB_TRANSFER_TYPE_ISOCHRONOUS}) ||
        in_endpoint.transfer_type != out_endpoint.transfer_type ||
        short_bytes == 0 || short_bytes >= in_endpoint.max_packet_size || short_bytes >= out_endpoint.max_packet_size) begin
      `uvm_fatal("USB_PERIODIC", "Require ordinary FS periodic IN/OUT endpoints and a useful short payload")
    end
    enable_endpoint_interrupt(in_endpoint);
    enable_endpoint_interrupt(out_endpoint);
    service_packet(in_endpoint, in_endpoint.max_packet_size, 8'h91);
    service_packet(out_endpoint, out_endpoint.max_packet_size, 8'h21);
    service_packet(in_endpoint, short_bytes, 8'hb1);
    service_packet(out_endpoint, short_bytes, 8'h41);
    completed = 1'b1;
    `uvm_info("USB_PERIODIC", "Full/short IN and OUT native periodic packets verified in separate frames", UVM_LOW)
  endtask
endclass
