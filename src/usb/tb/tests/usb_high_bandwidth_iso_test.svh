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

// Verifies high-bandwidth isochronous EP2 traffic in both directions.
class usb_high_bandwidth_iso_test extends usb_base_test;
  `uvm_component_utils(usb_high_bandwidth_iso_test)

  function new(string name = "usb_high_bandwidth_iso_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 4ms;
  endfunction

  // Advertise three-transaction high-speed isochronous EP2 IN and OUT.
  virtual function void configure_env_cfg(usb_env_cfg cfg);
    void'(cfg.add_endpoint(usb_endpoint_cfg::create_endpoint(
      "ep2_iso_out",
      2,
      USB_DIRECTION_OUT,
      USB_TRANSFER_TYPE_ISOCHRONOUS,
      1024,
      1,
      1'b0,
      -1,
      2
    )));
    void'(cfg.add_endpoint(usb_endpoint_cfg::create_endpoint(
      "ep2_iso_in",
      2,
      USB_DIRECTION_IN,
      USB_TRANSFER_TYPE_ISOCHRONOUS,
      1024,
      1,
      1'b0,
      -1,
      2
    )));
  endfunction

  task run_phase(uvm_phase phase);
    usb_high_bandwidth_iso_seq iso_sequence;

    phase.raise_objection(this);
    `uvm_info("USB_HB_ISO_TEST", $sformatf("Starting high-bandwidth ISO test; timeout=%0t", test_timeout), UVM_LOW)
    env.wait_for_reset();
    iso_sequence = usb_high_bandwidth_iso_seq::type_id::create("iso_sequence");
    iso_sequence.start(env.virtual_sequencer);
    scenario_completed = iso_sequence.completed;
    `uvm_info("USB_HB_ISO_TEST", "High-bandwidth ISO sequence returned; entering final UVM checks", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
