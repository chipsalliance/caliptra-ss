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

// Runs endpoint skip while EP1 OUT packet processing is being requested.
class usb_dev_skip_during_rx_test extends usb_base_test;
  `uvm_component_utils(usb_dev_skip_during_rx_test)

  function new(string name = "usb_dev_skip_during_rx_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 3ms;
  endfunction

  // EP2 buffers participate in active skip/writeback stress, so advertise them
  // through the same public enumeration fixture as EP1 before handing them to hardware.
  virtual function void configure_env_cfg(usb_env_cfg cfg);
    super.configure_env_cfg(cfg);
    void'(cfg.add_endpoint(usb_endpoint_cfg::create_endpoint(
      "ep2_skip_out", 2, USB_DIRECTION_OUT, USB_TRANSFER_TYPE_BULK, cfg.bulk_max_packet_size())));
    void'(cfg.add_endpoint(usb_endpoint_cfg::create_endpoint(
      "ep2_skip_in", 2, USB_DIRECTION_IN, USB_TRANSFER_TYPE_BULK, cfg.bulk_max_packet_size())));
    `uvm_info("USB_SKIP_RX_TEST", "Advertising EP2 OUT/IN for legal active word-half skip stress; EP1 packet scenario unchanged", UVM_LOW)
  endfunction

  task run_phase(uvm_phase phase);
    usb_dev_skip_during_rx_seq skip_sequence;

    phase.raise_objection(this);
    `uvm_info("USB_SKIP_RX_TEST", $sformatf("Starting endpoint skip-during-receive test; timeout=%0t", test_timeout), UVM_LOW)
    env.wait_for_reset();
    if (env.host_agent == null || env.host_agent.virt_sequencer == null) begin
      `uvm_fatal("USB_SKIP_RX_TEST", "The scenario requires an active SVT host agent")
    end

    skip_sequence = usb_dev_skip_during_rx_seq::type_id::create("skip_sequence");
    skip_sequence.start(env.virtual_sequencer);
    scenario_completed = skip_sequence.completed;
    `uvm_info("USB_SKIP_RX_TEST", "Skip-during-receive sequence returned; entering final UVM checks", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
