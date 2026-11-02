// SPDX-License-Identifier: Apache-2.0

// Runs the reusable double-buffer scenario at the configured speed.
class usb_double_buffer_bulk_test extends usb_base_test;
  `uvm_component_utils(usb_double_buffer_bulk_test)

  // Retain the source scenario's HS budget.
  function new(string name = "usb_double_buffer_bulk_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 3ms;
  endfunction

  // Own the objection until both native and device-side checks complete.
  task run_phase(uvm_phase phase);
    usb_double_buffer_bulk_seq sequence_handle;

    phase.raise_objection(this);
    `uvm_info("USB_DOUBLE_BUFFER_TEST", "Starting double-buffer scenario", UVM_LOW)
    env.wait_for_reset();
    sequence_handle = usb_double_buffer_bulk_seq::type_id::create("sequence_handle");
    sequence_handle.start(env.virtual_sequencer);
    scenario_completed = sequence_handle.completed;
    `uvm_info("USB_DOUBLE_BUFFER_TEST", "Double-buffer sequence returned; entering final checks", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
