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

class usb_ocp_dev1_epn_fs_overlap_seq extends usb_ocp_dev1_epn_overlap_seq;
  `uvm_object_utils(usb_ocp_dev1_epn_fs_overlap_seq)

  function new(string name = "usb_ocp_dev1_epn_fs_overlap_seq");
    super.new(name);
  endfunction

  function void ocp_check_fs_handshake_probe();
    usb_ocp_predictor control_probe;
    usb_ocp_base_epn_model epn_probe;
    usb_ocp_base_control probe_control;
    usb_ocp_event request;
    usb_ocp_event data;
    usb_ocp_event nyet;
    // Isolated checker input, never a native item, DUT event or live ledger.
    control_probe = usb_ocp_predictor::type_id::create("fs_control_probe");
    control_probe.full_speed = 1;
    probe_control = control_probe.control[0];
    probe_control.active = 1;
    probe_control.generation = 1;
    probe_control.setup = '{8'h80,svt_usb_types::GET_CONFIGURATION,0,0,0,0,1,0};
    probe_control.data = '{0};
    request = usb_ocp_event::type_id::create("private_out");
    request.host_tx = 1;
    request.pid = svt_usb_packet::OUT;
    request.packet_valid = 1;
    request.address = ocp_cfg.assigned_address[0];
    request.endpoint = 0;
    data = usb_ocp_event::type_id::create("private_status");
    data.host_tx = 1;
    data.pid = svt_usb_packet::DATA1;
    data.packet_valid = 1;
    control_probe.token = request;
    control_probe.candidate = data;
    control_probe.token_device = 0;
    control_probe.token_generation = probe_control.generation;
    nyet = usb_ocp_event::type_id::create("private_nyet");
    nyet.host_tx = 0;
    nyet.pid = svt_usb_packet::NYET;
    nyet.packet_valid = 1;
    `uvm_info("OCP_FS_CANARY", "Private FS control/EPN NYET probes must report twice and grant no acceptance",UVM_NONE)
    control_probe.ocp_observe_packet(nyet);
    if (!probe_control.active || probe_control.status_acked || probe_control.data.size() != 1 ||
        control_probe.token != null || control_probe.candidate != null)
      `uvm_fatal("OCP_FS_CANARY", "FS NYET changed private control acceptance")

    epn_probe = usb_ocp_base_epn_model::type_id::create("fs_epn_probe");
    epn_probe.payload_lengths = '{'{31,29},'{31,29}};
    epn_probe.device = 2;
    epn_probe.full_speed = 1;
    epn_probe.discovery.full_speed = 1;
    epn_probe.discovery.endpoints[0] = usb_endpoint_cfg::create_endpoint(
      "private_fs_bulk",1,USB_DIRECTION_OUT,USB_TRANSFER_TYPE_BULK,64,1);
    epn_probe.enabled = 1;
    epn_probe.address = ocp_cfg.assigned_address[2];
    epn_probe.control_address = ocp_cfg.assigned_address[1];
    probe_control = usb_ocp_base_control::type_id::create("private_ocp_context");
    probe_control.active = 1;
    probe_control.generation = 1;
    probe_control.address = epn_probe.control_address;
    probe_control.setup = '{8'ha1,OCP_BREQUEST_XFER,8'(OCP_CMD_PROT_CAP),
      8'(OCP_CMD_PROT_CAP >> 8),0,0,64,0};
    request.address = epn_probe.address;
    request.endpoint = 1;
    data.pid = svt_usb_packet::DATA0;
    data.bytes = usb_ocp_base_epn_profile::ocp_prepare_stream(
      USB_DIRECTION_OUT,0,epn_probe.payload_lengths[0][0]);
    epn_probe.ocp_observe_packet(request,probe_control);
    epn_probe.ocp_observe_packet(data,probe_control);
    epn_probe.ocp_observe_packet(nyet,probe_control);
    if (epn_probe.accepted[0] != 0 || epn_probe.next_toggle[0] !== 0 ||
        epn_probe.token != null || epn_probe.candidate != null)
      `uvm_fatal("OCP_FS_CANARY", "FS NYET changed private EPN acceptance/toggle")
  endfunction

  task body();
    if (!ocp_cfg.full_speed ||
        !uvm_config_db#(usb_ocp_scoreboard)::get(p_sequencer,"","ocp_scoreboard",scoreboard))
      `uvm_fatal("OCP_FS_CONFIG", "FS scenario requires its owned configuration and passive checker")
    scoreboard.model.full_speed = 1;
    if ($test$plusargs("usb_ocp_negative_fs_handshake"))
      ocp_check_fs_handshake_probe();
    super.body();
  endtask
endclass
