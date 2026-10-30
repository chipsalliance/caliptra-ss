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

class usb_test_modes_test extends usb_base_test;
  `uvm_component_utils(usb_test_modes_test)

  function new(string name = "usb_test_modes_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    usb_test_modes_seq sequence_handle;

    phase.raise_objection(this);
    env.wait_for_reset();
    sequence_handle = usb_test_modes_seq::type_id::create("test_modes_sequence");
    if (!$value$plusargs("usb_test_mode=%s", sequence_handle.mode_name)) begin
      `uvm_fatal("USB_TEST_MODES", "Select one electrical mode with +usb_test_mode=TEST_J|TEST_K|TEST_SE0_NAK")
    end
    sequence_handle.start(env.virtual_sequencer);
    scenario_completed = sequence_handle.completed;
    phase.drop_objection(this);
  endtask
endclass
