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

class usb_ocp_base_epn_overlap_seq extends usb_ocp_bringup_seq;
  `uvm_object_utils(usb_ocp_base_epn_overlap_seq)
  usb_ocp_scoreboard scoreboard;
  int unsigned epn_device = 1;

  function new(string name = "usb_ocp_base_epn_overlap_seq");
    super.new(name);
  endfunction

  virtual function usb_ocp_base_host_seq ocp_prepare_host();
    usb_ocp_base_epn_overlap_host_seq host;
    host = usb_ocp_base_epn_overlap_host_seq::type_id::create("host");
    host.epn_device = epn_device;
    host.scoreboard = scoreboard;
    return host;
  endfunction

  function void ocp_check_nak_probe();
    usb_ocp_base_epn_model probe;
    usb_ocp_base_epn_profile profile;
    usb_ocp_base_control probe_control;
    usb_ocp_event first_poll;
    usb_ocp_event nak;
    usb_ocp_event early_poll;
    // An isolated checker control, not USB stimulus or a DUT/model actual.
    // Native legal scheduling cannot be used to manufacture an illegal poll.
    profile = usb_ocp_base_epn_profile::type_id::create("nak_probe_profile");
    profile.device = epn_device;
    profile.full_speed = ocp_cfg.full_speed;
    profile.transfer_type = USB_TRANSFER_TYPE_INTERRUPT;
    profile.payload_lengths = '{'{31,29},'{31,29}};
    profile.payload_lengths_selected = 1;
    probe = usb_ocp_base_epn_model::type_id::create("nak_probe");
    probe.payload_lengths = profile.payload_lengths;
    probe.full_speed = ocp_cfg.full_speed;
    probe.discovery.full_speed = ocp_cfg.full_speed;
    probe.device = epn_device;
    probe.discovery.ocp_check_parse(profile.ocp_prepare_descriptor(epn_device,16'h0200));
    probe.enabled = 1;
    probe.address = ocp_cfg.assigned_address[epn_device];
    probe.control_address = ocp_cfg.assigned_address[1];
    probe.sof_seen = 1;
    probe.last_sof_serial = 1;
    probe_control = usb_ocp_base_control::type_id::create("nak_probe_context");
    probe_control.active = 1;
    probe_control.generation = 1;
    probe_control.address = probe.control_address;
    probe_control.setup = '{8'ha1,OCP_BREQUEST_XFER,8'(OCP_CMD_PROT_CAP),
      8'(OCP_CMD_PROT_CAP >> 8),0,0,64,0};
    first_poll = usb_ocp_event::type_id::create("nak_probe_first_poll");
    first_poll.host_tx = 1;
    first_poll.pid = svt_usb_packet::IN;
    first_poll.packet_valid = 1;
    first_poll.address = probe.address;
    first_poll.endpoint = 4'(probe.discovery.endpoints[1].ep_number);
    first_poll.sof_serial = 1;
    probe.ocp_observe_packet(first_poll,probe_control);
    nak = usb_ocp_event::type_id::create("nak_probe_nak");
    nak.host_tx = 0;
    nak.pid = svt_usb_packet::NAK;
    nak.packet_valid = 1;
    nak.sof_serial = 1;
    probe.ocp_observe_packet(nak,probe_control);
    early_poll = usb_ocp_event::type_id::create("nak_probe_early_poll");
    early_poll.host_tx = 1;
    early_poll.pid = svt_usb_packet::IN;
    early_poll.packet_valid = 1;
    early_poll.address = probe.address;
    early_poll.endpoint = first_poll.endpoint;
    early_poll.sof_serial = 1;
    `uvm_info("OCP_EPN_CANARY", "Private IN/NAK/IN same-opportunity probe must fail OCP_EPN_INTERVAL; no native traffic",UVM_NONE)
    probe.ocp_observe_packet(early_poll,probe_control);
    `uvm_fatal("OCP_EPN_CANARY", "Interrupt checker failed to reject premature NAK re-polling")
  endfunction

  task body();
    usb_ocp_base_epn_profile profile;
    uvm_reg_map memory_map;
    if (!uvm_config_db#(usb_ocp_scoreboard)::get(p_sequencer,"","ocp_scoreboard",scoreboard))
      `uvm_fatal("OCP_EPN_PROFILE", "Missing mandatory passive checker")
    if (!(epn_device inside {1,2}))
      `uvm_fatal("OCP_EPN_PROFILE", "Only device0 or device1 USB2 EPN ownership is supported")
    profile = usb_ocp_base_epn_profile::type_id::create("firmware_profile");
    profile.device = epn_device;
    profile.full_speed = ocp_cfg.full_speed;
    // One type per run, one row. No flags or profile constants discover USB.
    profile.transfer_type = usb_ocp_base_epn_profile::ocp_prepare_selected_type();
    profile.ocp_prepare_payload_lengths();
    if (scoreboard.negative_overlap || scoreboard.negative_replacement ||
        scoreboard.negative_abort_prefix)
      `uvm_fatal("OCP_NEGATIVE_CONTROL", "EP0-specific injection is unsupported by the EPN profile")
    if (scoreboard.negative_epn_nak) begin
      if (profile.transfer_type != USB_TRANSFER_TYPE_INTERRUPT)
        `uvm_fatal("OCP_NEGATIVE_CONTROL", "NAK checker control requires the INTERRUPT EPN profile")
      ocp_check_nak_probe();
    end
    ocp_cfg.epn_profiles[epn_device-1] = profile;
    memory_map = map_for((epn_device == 1) ? USB_DEV0_SRAM : USB_DEV1_SRAM);
    scoreboard.model.ocp_configure_epn_profile(profile,ocp_cfg.endpoint_list_base,
      memory_map.get_base_addr(UVM_NO_HIER),scoreboard.negative_epn_payload);
    `uvm_info("OCP_EPN_PROFILE",$sformatf(
      "Test-owned firmware type=%s; host must discover it over USB",
      profile.transfer_type.name()),UVM_LOW)
    super.body();
  endtask
endclass
