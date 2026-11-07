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

class usb_ocp_mixed_traffic_seq extends usb_ocp_bringup_seq;
  `uvm_object_utils(usb_ocp_mixed_traffic_seq)
  usb_ocp_scoreboard scoreboard;

  function new(string name = "usb_ocp_mixed_traffic_seq");
    super.new(name);
  endfunction

  virtual function usb_ocp_base_host_seq ocp_prepare_host();
    usb_ocp_mixed_traffic_host_seq host;
    host = usb_ocp_mixed_traffic_host_seq::type_id::create("host");
    host.scoreboard = scoreboard;
    return host;
  endfunction

  task body();
    usb_ocp_base_epn_profile profile;
    usb_transfer_type_e selected_type;
    uvm_reg_map memory_map;
    if (!uvm_config_db#(usb_ocp_scoreboard)::get(p_sequencer,"","ocp_scoreboard",scoreboard))
      `uvm_fatal("OCP_MIXED_PROFILE", "Missing mandatory passive checker")
    if (scoreboard.negative_overlap || scoreboard.negative_abort_prefix ||
        scoreboard.negative_epn_nak)
      `uvm_fatal("OCP_NEGATIVE_CONTROL", "Dev1 EP0, nonzero prefix and isolated NAK controls are unsupported by mixed")
    selected_type = usb_ocp_base_epn_profile::ocp_prepare_selected_type();
    for (int device = 1; device <= 2; device++) begin
      profile = usb_ocp_base_epn_profile::type_id::create($sformatf("firmware_profile%0d",device));
      profile.device = device;
      profile.transfer_type = selected_type;
      profile.data_tag = 64*device;
      ocp_cfg.epn_profiles[device-1] = profile;
      memory_map = map_for((device == 1) ? USB_DEV0_SRAM : USB_DEV1_SRAM);
      scoreboard.model.ocp_configure_epn_profile(profile,ocp_cfg.endpoint_list_base,
        memory_map.get_base_addr(UVM_NO_HIER),scoreboard.negative_epn_payload);
    end
    scoreboard.model.require_mixed_epn = 1;
    scoreboard.model.require_dev0_ep0_replacement = 1;
    scoreboard.mixed_stream_cov.option.weight = 1;
    `uvm_info("OCP_MIXED_PROFILE",$sformatf(
      "Both device-owned firmware pairs type=%s; real USB discovery and eight streams required",
      selected_type.name()),UVM_LOW)
    super.body();
  endtask
endclass
