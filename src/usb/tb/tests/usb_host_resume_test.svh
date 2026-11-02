// SPDX-License-Identifier: Apache-2.0

// Retain the native HS scaled preset. FS reuses the candidate external-DUT
// downstream budget with passive admission, not nominal timing signoff.
class usb_host_resume_cfg_builder extends usb_vip_cfg_builder;
  `uvm_object_utils(usb_host_resume_cfg_builder)

  // Construct a factory-overridable native timing policy.
  function new(string name = "usb_host_resume_cfg_builder");
    super.new(name);
  endfunction

  // Change only FS downstream compatibility and native recovery SOF policy.
  protected virtual function void configure_timers();
    super.configure_timers();
    if (bus_speed == USB_SPEED_FULL) begin
      usb_l2_remote_wake_cfg_builder::apply_downstream_resume_budget(host_cfg);
      usb_l2_remote_wake_cfg_builder::apply_downstream_resume_budget(device_phy_cfg);
      host_cfg.enable_sof_during_recovery = 1'b1;
    end
  endfunction
endclass

// One scenario selector for both host-resume power states and bus speeds.
class usb_host_resume_test extends usb_base_test;
  `uvm_component_utils(usb_host_resume_test)

  bit l1 = 1'b1;

  // Preserve the original HS host-resume whole-test budget.
  function new(string name = "usb_host_resume_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 3ms;
  endfunction

  // Reuse the reviewed L1 policy and speed-specific native L2 overlay.
  function void build_phase(uvm_phase phase);
    if (l1) usb_vip_cfg_builder::type_id::set_type_override(usb_l1_remote_wake_vip_cfg_builder::get_type());
    else usb_vip_cfg_builder::type_id::set_type_override(usb_host_resume_cfg_builder::get_type());
    super.build_phase(phase);
  endfunction

  // Run shared orchestration without test-local observations or comparisons.
  task run_phase(uvm_phase phase);
    usb_host_resume_seq sequence_handle;
    phase.raise_objection(this);
    `uvm_info("USB_HOST_RESUME_TEST", $sformatf("Starting L%0d host-resume scenario", l1 ? 1 : 2), UVM_LOW)
    env.wait_for_reset();
    sequence_handle = usb_host_resume_seq::type_id::create("sequence_handle");
    sequence_handle.l1 = l1;
    if (env_cfg.speed == USB_SPEED_FULL) sequence_handle.suspend_timeout = l1 ? USB_FS_L1_CYCLE_TIMEOUT : USB_FS_L2_HOST_CYCLE_TIMEOUT;
    else sequence_handle.suspend_timeout = l1 ? 2ms : 750us;
    sequence_handle.start(env.virtual_sequencer);
    scenario_completed = sequence_handle.completed;
    `uvm_info("USB_HOST_RESUME_TEST", "Host-resume sequence returned; entering final checks", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass

// Focused HS regression selector for the generalized L1 scenario.
class usb_l1_host_resume_test extends usb_host_resume_test;
  `uvm_component_utils(usb_l1_host_resume_test)
  // Select the reviewed L1 budget; HS remains the configuration default.
  function new(string name = "usb_l1_host_resume_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 5ms;
  endfunction
endclass

// Focused HS regression selector for the generalized L2 scenario.
class usb_l2_host_resume_test extends usb_host_resume_test;
  `uvm_component_utils(usb_l2_host_resume_test)
  // Select native L2 entry/resume before configuration construction.
  function new(string name = "usb_l2_host_resume_test", uvm_component parent = null);
    super.new(name, parent);
    l1 = 1'b0;
  endfunction
endclass
