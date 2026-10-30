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

class usb_l1_remote_wake_vip_cfg_builder extends usb_vip_cfg_builder;
  `uvm_object_utils(usb_l1_remote_wake_vip_cfg_builder)

  function new(string name = "usb_l1_remote_wake_vip_cfg_builder");
    super.new(name);
  endfunction

  protected virtual function void configure_timers();
    super.configure_timers();
    restore_lpm_timers(host_cfg);
    restore_lpm_timers(device_phy_cfg);
  endfunction

  // Restore drive and checker limits together after the shared scaled preset.
  // USB 2.0 LPM ECN section 4.9, Table 4-6; SVT configuration tl1* members.
  function void restore_lpm_timers(svt_usb_configuration cfg);
    // The BOS fixture advertises legacy LPM, and host resume sends HIRD=1.
    // SVT's configuration reference requires programming the ECN drive explicitly.
    cfg.select_lpm_errata_mode = 1'b0;
    cfg.tl1hubdrvresume1 = vip_ps(125us);
    cfg.tl1hubdrvresume1_min = vip_ps(124us);
    cfg.tl1hubdrvresume1_max = vip_ps(126us);
    cfg.tl1tokenretry = vip_ps(8us);
    cfg.tl1tokenretry_min = vip_ps(8us);
    cfg.tl1residency = vip_ps(50us);
    cfg.tl1residency_min = vip_ps(50us);
    cfg.tl1residency_max = vip_ps(55us);
    cfg.tl1devdrvresume = vip_ps(50us);
    cfg.tl1devdrvresume_min = vip_ps(50us);
    cfg.tl1hubreflect = vip_ps(30us);
    cfg.tl1hubreflect_min = vip_ps(30us);
    cfg.tl1hubreflect_max = vip_ps(48us);
    cfg.tl1hubdrvresume2 = vip_ps(60us);
    cfg.tl1hubdrvresume2_min = vip_ps(60us);
    cfg.tl1hubdrvresume2_max = vip_ps(990us);
    cfg.tl1exitdevrecovery = vip_ps(10us);
    cfg.tl1exitdevrecovery_min = vip_ps(10us);
    `uvm_info("USB_L1_CFG", $sformatf("Legacy LPM HIRD=1 policy: host drive/check bounds=%0.0f/%0.0f/%0.0f ps",
      cfg.tl1hubdrvresume1, cfg.tl1hubdrvresume1_min, cfg.tl1hubdrvresume1_max), UVM_LOW)
  endfunction
endclass
