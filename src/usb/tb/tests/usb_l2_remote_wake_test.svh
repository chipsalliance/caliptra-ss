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

// Verify authorized device-origin L2 wake with the selected bus speed.
class usb_l2_remote_wake_test extends usb_base_test;
  `uvm_component_utils(usb_l2_remote_wake_test)

  function new(string name = "usb_l2_remote_wake_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 60ms;
  endfunction

  virtual function time full_speed_timeout();
    return USB_FS_ENUMERATION_BUDGET + USB_FS_WAKE_PERMISSION_BUDGET + 35ms + USB_FS_TRANSFER_TIMEOUT + USB_FS_FRAME_PERIOD;
  endfunction

  function void build_phase(uvm_phase phase);
    usb_vip_cfg_builder::type_id::set_type_override(usb_l2_remote_wake_cfg_builder::get_type());
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    usb_l2_remote_wake_seq sequence_handle;

    phase.raise_objection(this);
    env.wait_for_reset();
    sequence_handle = usb_l2_remote_wake_seq::type_id::create("remote_wake_sequence");
    sequence_handle.start(env.virtual_sequencer);
    scenario_completed = sequence_handle.completed;
    phase.drop_objection(this);
  endtask
endclass
