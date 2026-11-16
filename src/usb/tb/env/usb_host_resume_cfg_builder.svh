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
