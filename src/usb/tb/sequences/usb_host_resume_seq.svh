// SPDX-License-Identifier: Apache-2.0

// Generalizes the device-side L1/L2 host-resume scenarios without FS clones.
// Reuses shared BOS discovery, CSR polling and checked bulk recovery.
class usb_host_resume_seq extends usb_resume_recovery_seq;
  `uvm_object_utils(usb_host_resume_seq)

  bit l1 = 1'b1;
  time suspend_timeout = 750us;
  bit completed;

  // Construct the reusable host-resume orchestration.
  function new(string name = "usb_host_resume_seq");
    super.new(name);
  endfunction

  // Enumerate, qualify native/DUT entry, observe host exit and recover traffic.
  virtual task body();
    usb_init_seq init_sequence;
    usb_lpm_capability_host_seq discovery;
    usb_host_resume_host_seq host_sequence;
    uvm_event dut_suspended;
    uvm_event host_ready;
    uvm_event recovery_complete;
    logic [31:0] command;
    logic [31:0] suspend_mask;
    logic [31:0] address_mask;
    logic [31:0] address_before;
    int unsigned request_count;

    completed = 1'b0;
    `uvm_info("USB_HOST_RESUME", $sformatf("Starting L%0d host resume; running shared enumeration", l1 ? 1 : 2), UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.lpm_supported = l1;
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) `uvm_fatal("USB_HOST_RESUME", "Enumeration incomplete")
    if (l1) begin
      `uvm_info("USB_HOST_RESUME", "Discovering LPM capability on wire with concurrent EP0 service", UVM_LOW)
      discovery = usb_lpm_capability_host_seq::type_id::create("discovery");
      discovery.control_endpoint = get_endpoint(0, USB_DIRECTION_OUT);
      discovery.device_address = p_sequencer.cfg.device_address;
      discovery.control_transfer_timeout = p_sequencer.cfg.control_transfer_timeout;
      request_count = init_sequence.serviced_request_count + usb_lpm_capability_host_seq::DISCOVERY_REQUEST_COUNT;
      fork
        discovery.start(p_sequencer.host_sequencer);
        init_sequence.service_ep0(request_count);
      join
      if (!discovery.completed || init_sequence.serviced_request_count != request_count) begin
        `uvm_fatal("USB_HOST_RESUME", "On-wire LPM capability discovery incomplete")
      end
      `uvm_info("USB_HOST_RESUME", "LPM capability discovered; proceeding to native suspend", UVM_LOW)
    end
    suspend_mask = l1 ? ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.LPM_SUS) :
                        ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.DSUS);
    address_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.DEV_ADDR);
    ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    address_before = command & address_mask;
    dut_suspended = new("dut_suspended");
    host_ready = new("host_ready");
    recovery_complete = new("recovery_complete");
    host_sequence = usb_host_resume_host_seq::type_id::create("host_sequence");
    host_sequence.l1 = l1;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.link_state_timeout = suspend_timeout;
    host_sequence.dut_suspended = dut_suspended;
    host_sequence.host_ready = host_ready;
    host_sequence.recovery_complete = recovery_complete;
    host_sequence.guard_fs_l2 = !l1 && p_sequencer.cfg.speed == USB_SPEED_FULL;
    host_sequence.ctrl_vif = p_sequencer.ctrl_vif;
    fork
      host_sequence.start(p_sequencer.host_sequencer);
      begin
        poll_csr_bits("DUT suspend entry", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT,
                      suspend_mask, 1'b1, suspend_timeout, command);
        `uvm_info("USB_HOST_RESUME", $sformatf("DUT L%0d entry observed: DEVCMDSTAT=%08h", l1 ? 1 : 2, command), UVM_LOW)
        dut_suspended.trigger();
        poll_csr_bits("DUT suspend exit", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT,
                      suspend_mask, 1'b0, suspend_timeout, command);
        `uvm_info("USB_HOST_RESUME", $sformatf("DUT L%0d exit observed: DEVCMDSTAT=%08h", l1 ? 1 : 2, command), UVM_LOW)
        `uvm_info("USB_HOST_RESUME", "DUT exit observed; waiting for native host recovery admission", UVM_LOW)
        host_ready.wait_on();
        ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
        if (!((command & suspend_mask) === 32'b0)) `uvm_fatal("USB_HOST_RESUME", "DUT suspend reasserted before bulk admission")
        if (!((command & address_mask) === address_before)) `uvm_fatal("USB_HOST_RESUME", "Device address changed across host resume")
        // The shared recovery helper verifies live public speed before arming.
        recovery_timeout = 750us;
        run_recovery_transfer("Post-host-resume bulk OUT");
        recovery_complete.trigger();
      end
    join
    if (!host_sequence.completed) `uvm_fatal("USB_HOST_RESUME", "Native host resume incomplete")
    completed = 1'b1;
    `uvm_info("USB_HOST_RESUME", "Host-origin resume, DUT transitions, speed/address and checked recovery verified", UVM_LOW)
  endtask
endclass
