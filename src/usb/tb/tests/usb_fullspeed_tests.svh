// SPDX-License-Identifier: Apache-2.0

// Configuration-only speed specialization; all scenarios/checkers remain shared.
class usb_fullspeed_test_base #(type BASE = usb_init_test) extends BASE;
  `uvm_component_param_utils(usb_fullspeed_test_base #(BASE))

  // Start with a request-count-derived enumeration guard; selectors add work.
  function new(string name = "usb_fullspeed_test_base", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = USB_FS_ENUMERATION_BUDGET;
  endfunction

  // Select a real FS host bus and rebuild coherent endpoint defaults.
  virtual function void configure_env_cfg(usb_env_cfg cfg);
    super.configure_env_cfg(cfg);
    cfg.select_full_speed();
  endfunction
endclass

// FS enumeration retains shared EP0 discovery and live DUT speed acceptance.
class usb_fs_init_test extends usb_fullspeed_test_base #(usb_init_test);
  `uvm_component_utils(usb_fs_init_test)
  // Construct the concrete selector.
  function new(string name = "usb_fs_init_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
endclass

// FS static skip retains the existing skip writeback/recovery scenario.
class usb_fs_dev_skip_test extends usb_fullspeed_test_base #(usb_dev_skip_test);
  `uvm_component_utils(usb_fs_dev_skip_test)
  // Construct the concrete selector.
  function new(string name = "usb_fs_dev_skip_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = USB_FS_ENUMERATION_BUDGET + USB_FS_TRANSFER_TIMEOUT + USB_FS_FRAME_PERIOD;
  endfunction
endclass

// FS double buffering covers full/full and full/13-byte packet pairs.
class usb_fs_double_buffer_bulk_test extends usb_fullspeed_test_base #(usb_double_buffer_bulk_test);
  `uvm_component_utils(usb_fs_double_buffer_bulk_test)
  // Construct the concrete selector.
  function new(string name = "usb_fs_double_buffer_bulk_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = USB_FS_ENUMERATION_BUDGET + 4 * USB_FS_BULK_PAIR_TIMEOUT + USB_FS_FRAME_PERIOD;
  endfunction
endclass

// FS ordinary interrupt packets use the common native periodic helper.
class usb_fs_interrupt_test extends usb_periodic_test;
  `uvm_component_utils(usb_fs_interrupt_test)
  // Construct the concrete selector.
  function new(string name = "usb_fs_interrupt_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
endclass

// FS ordinary ISO packets do not inherit HS partial-service expectations.
class usb_fs_iso_test extends usb_periodic_test;
  `uvm_component_utils(usb_fs_iso_test)
  // Select ISO metadata before shared configuration construction.
  function new(string name = "usb_fs_iso_test", uvm_component parent = null);
    super.new(name, parent);
    periodic_type = USB_TRANSFER_TYPE_ISOCHRONOUS;
  endfunction
endclass

// FS L1 host resume uses shared BOS discovery and native host-origin observation.
class usb_fs_l1_host_resume_test extends usb_fullspeed_test_base #(usb_host_resume_test);
  `uvm_component_utils(usb_fs_l1_host_resume_test)
  // Select the L1 timing budget before build_phase.
  function new(string name = "usb_fs_l1_host_resume_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = USB_FS_ENUMERATION_BUDGET + USB_FS_LPM_DISCOVERY_BUDGET +
      USB_FS_L1_CYCLE_TIMEOUT + USB_FS_TRANSFER_TIMEOUT + USB_FS_FRAME_PERIOD;
  endfunction
endclass

// FS L2 host resume uses native downstream signaling and checked bulk recovery.
class usb_fs_l2_host_resume_test extends usb_fullspeed_test_base #(usb_host_resume_test);
  `uvm_component_utils(usb_fs_l2_host_resume_test)
  // Select the L2 native services before build_phase.
  function new(string name = "usb_fs_l2_host_resume_test", uvm_component parent = null);
    super.new(name, parent);
    l1 = 1'b0;
    // Include native inactivity, candidate drive, SOFs and frame-aware bulk.
    test_timeout = USB_FS_ENUMERATION_BUDGET + USB_FS_L2_HOST_CYCLE_TIMEOUT + USB_FS_FRAME_PERIOD;
  endfunction
endclass

// FS L1 device wake retains existing permission and native-origin checks.
class usb_fs_l1_remote_wake_test extends usb_fullspeed_test_base #(usb_l1_remote_wake_test);
  `uvm_component_utils(usb_fs_l1_remote_wake_test)
  // Construct the concrete selector.
  function new(string name = "usb_fs_l1_remote_wake_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = USB_FS_ENUMERATION_BUDGET + USB_FS_LPM_DISCOVERY_BUDGET +
      USB_FS_L1_CYCLE_TIMEOUT + USB_FS_TRANSFER_TIMEOUT + USB_FS_FRAME_PERIOD;
  endfunction
endclass

// FS L2 device wake retains actual gating/EOR/SOF proof and scaled recovery.
class usb_fs_l2_remote_wake_test extends usb_fullspeed_test_base #(usb_l2_remote_wake_test);
  `uvm_component_utils(usb_fs_l2_remote_wake_test)
  // Construct the concrete selector.
  function new(string name = "usb_fs_l2_remote_wake_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = USB_FS_ENUMERATION_BUDGET + USB_FS_WAKE_PERMISSION_BUDGET + 35ms + USB_FS_TRANSFER_TIMEOUT + USB_FS_FRAME_PERIOD;
  endfunction
endclass
