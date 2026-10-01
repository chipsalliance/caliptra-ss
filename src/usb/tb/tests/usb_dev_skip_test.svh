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
//
// Runs the standalone USB endpoint-skip scenario against the real compound USB
// DUT, driving the USB DMA through its READ_EPINFO_SKIP and
// WAIT_ON_GNT_FOR_SKIP_UPDATE states. The target endpoint (EP1 OUT) is resolved
// by protocol identity from the default usb_env_cfg endpoint configuration.
//
// Starts usb_dev_skip_seq on the environment virtual sequencer and reports
// success only after the skip writeback and the post-skip recovery transfer
// have both been verified.
class usb_dev_skip_test extends usb_base_test;
  `uvm_component_utils(usb_dev_skip_test)

  function new(string name = "usb_dev_skip_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 3ms;
  endfunction

  task run_phase(uvm_phase phase);
    usb_dev_skip_seq skip_sequence;

    phase.raise_objection(this);
    `uvm_info("USB_SKIP_TEST", $sformatf("Starting real-traffic USB endpoint-skip test; timeout=%0t", test_timeout), UVM_LOW)
    env.wait_for_reset();
    if (env.host_agent == null || env.host_agent.virt_sequencer == null) begin
      `uvm_fatal("USB_SKIP_TEST", "The endpoint-skip scenario requires an active SVT host agent")
    end

    skip_sequence = usb_dev_skip_seq::type_id::create("skip_sequence");
    skip_sequence.start(env.virtual_sequencer);
    scenario_completed = skip_sequence.completed;
    `uvm_info("USB_SKIP_TEST", "USB endpoint-skip sequence returned; entering final UVM checks", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
