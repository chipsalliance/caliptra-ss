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

// Verifies two-buffer transfers, with optional same-sequence response stress.
class usb_double_buffer_bulk_test extends usb_base_test;
  `uvm_component_utils(usb_double_buffer_bulk_test)

  int unsigned response_stress_count = 0;

  function new(string name = "usb_double_buffer_bulk_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 3ms;
  endfunction

  // Resolve optional response stress before the base applies the test timeout.
  virtual function void build_phase(uvm_phase phase);
    if ($value$plusargs("usb_bulk_response_stress_count=%d", response_stress_count)) begin
      if (response_stress_count < 9 || response_stress_count > 64) begin
        `uvm_fatal("USB_BULK_RESPONSE_STRESS", "usb_bulk_response_stress_count must be in [9,64]")
      end
      test_timeout *= response_stress_count;
    end
    super.build_phase(phase);
    `uvm_info("USB_BULK_RESPONSE_STRESS",
              $sformatf("Configured extra transfers per active bulk sequence: %0d; whole-test timeout=%0t",
                        response_stress_count, test_timeout), UVM_LOW)
  endfunction

  virtual function time full_speed_timeout();
    return USB_FS_ENUMERATION_BUDGET + (4 + 2 * response_stress_count) * USB_FS_BULK_PAIR_TIMEOUT + USB_FS_FRAME_PERIOD;
  endfunction

  task run_phase(uvm_phase phase);
    usb_double_buffer_bulk_seq double_buffer_sequence;

    phase.raise_objection(this);
    `uvm_info("USB_DOUBLE_BUFFER_TEST", $sformatf("Starting double-buffer bulk test; timeout=%0t", test_timeout), UVM_LOW)
    env.wait_for_reset();
    double_buffer_sequence = usb_double_buffer_bulk_seq::type_id::create("double_buffer_sequence");
    double_buffer_sequence.response_stress_count = response_stress_count;
    double_buffer_sequence.start(env.virtual_sequencer);
    scenario_completed = double_buffer_sequence.completed;
    `uvm_info("USB_DOUBLE_BUFFER_TEST", "Double-buffer sequence returned; entering final UVM checks", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
