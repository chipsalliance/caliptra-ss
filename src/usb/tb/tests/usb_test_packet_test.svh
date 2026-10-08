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

// Verifies the complete high-speed TEST_PACKET waveform at the UTMI boundary.
class usb_test_packet_test extends usb_base_test;
  `uvm_component_utils(usb_test_packet_test)

  function new(string name = "usb_test_packet_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 2ms;
  endfunction

  task run_phase(uvm_phase phase);
    usb_test_packet_seq test_packet_sequence;

    phase.raise_objection(this);
    `uvm_info("USB_TEST_PACKET_TEST", $sformatf("Starting TEST_PACKET test; timeout=%0t", test_timeout), UVM_LOW)
    env.wait_for_reset();
    test_packet_sequence = usb_test_packet_seq::type_id::create("test_packet_sequence");
    test_packet_sequence.start(env.virtual_sequencer);
    scenario_completed = test_packet_sequence.completed;
    `uvm_info("USB_TEST_PACKET_TEST", "TEST_PACKET sequence returned; entering final UVM checks", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
