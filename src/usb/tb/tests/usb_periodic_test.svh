// SPDX-License-Identifier: Apache-2.0

// Selects an ordinary FS periodic layout without duplicating scenarios.
class usb_periodic_test extends usb_base_test;
  `uvm_component_utils(usb_periodic_test)

  usb_transfer_type_e periodic_type = USB_TRANSFER_TYPE_INTERRUPT;

  // Four separately scheduled frames plus enumeration and checking.
  function new(string name = "usb_periodic_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = USB_FS_ENUMERATION_BUDGET + 4 * USB_FS_PERIODIC_TRANSFER_TIMEOUT + USB_FS_FRAME_PERIOD;
  endfunction

  // Keep descriptor bInterval=1 and isoc_mult=0; builder maps native metadata.
  virtual function void configure_env_cfg(usb_env_cfg cfg);
    int unsigned mps;
    cfg.select_full_speed();
    mps = periodic_type == USB_TRANSFER_TYPE_ISOCHRONOUS ? `SVT_USB_FS_ISOC_MAX_PACKET_SIZE : `SVT_USB_FS_INTR_MAX_PACKET_SIZE;
    cfg.endpoint_cfgs.delete();
    void'(cfg.add_endpoint(usb_endpoint_cfg::create_endpoint("ep1_periodic_in", 1, USB_DIRECTION_IN, periodic_type, mps, 1, 1'b1, 0, 0)));
    void'(cfg.add_endpoint(usb_endpoint_cfg::create_endpoint("ep1_periodic_out", 1, USB_DIRECTION_OUT, periodic_type, mps, 1, 1'b1, 0, 0)));
  endfunction

  // Keep stimulus and checking in their reusable sequences and native VIP.
  task run_phase(uvm_phase phase);
    usb_periodic_seq sequence_handle;
    phase.raise_objection(this);
    `uvm_info("USB_PERIODIC_TEST", $sformatf("Starting ordinary FS %s scenario", periodic_type.name()), UVM_LOW)
    env.wait_for_reset();
    sequence_handle = usb_periodic_seq::type_id::create("sequence_handle");
    sequence_handle.start(env.virtual_sequencer);
    scenario_completed = sequence_handle.completed;
    `uvm_info("USB_PERIODIC_TEST", "Periodic sequence returned; entering final checks", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
