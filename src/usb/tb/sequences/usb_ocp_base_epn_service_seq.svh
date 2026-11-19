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

// MCU/SoC-local endpoint SRAM service. Public endpoint_entry geometry is
// reused, while the selected actor's memory target preserves device ownership.
class usb_ocp_base_epn_service_seq extends usb_ocp_base_seq;
  `uvm_object_utils(usb_ocp_base_epn_service_seq)
  usb_ocp_base_epn_profile profile;
  int unsigned device;
  usb_target_e memory_target;
  usb_endpoint_cfg endpoints[2];
  int unsigned phase[2];

  function new(string name = "usb_ocp_base_epn_service_seq");
    super.new(name);
    phase = '{default:0};
  endfunction

  task ocp_do_arm(int dir);
    usb_ep_entry_t entry;
    logic [31:0] word;
    logic [31:0] buffer_offset;
    usb_direction_e direction;
    usb_ocp_base_epn_profile::bytes_t data;
    direction = dir ? USB_DIRECTION_IN : USB_DIRECTION_OUT;
    data = usb_ocp_base_epn_profile::ocp_prepare_stream(direction,phase[dir]);
    buffer_offset = usb_ocp_base_epn_profile::ocp_get_buffer(direction);
    check_buffer_clear_of_endpoint_list("OCP EPN",buffer_offset,64);
    for (int i = 0; i < data.size(); i += 4) begin
      word = 32'heeee_eeee;
      for (int j = 0; j < 4 && i+j < data.size(); j++)
        if (dir == 1) word[j*8+:8] = data[i+j];
      write32(memory_target,buffer_offset+i,word);
    end
    entry = endpoint_entry(1,0,data.size(),buffer_offset);
    // Generic BULK T=0; periodic ISO T=1/RF=0; periodic INT T=1/RF=1.
    entry.ep_type = (endpoints[dir].transfer_type != USB_TRANSFER_TYPE_BULK);
    entry.toggle_value = (endpoints[dir].transfer_type == USB_TRANSFER_TYPE_INTERRUPT);
    write32(memory_target,endpoint_list_base()+endpoints[dir].entry_offset(),entry);
    ocp_cfg.epn_ready[device-1][phase[dir]][dir] = 1;
  endtask

  task ocp_do_check_retirement(int dir, output bit progress);
    logic [31:0] word;
    usb_ep_entry_t entry;
    usb_ocp_base_epn_profile::bytes_t data;
    logic [31:0] buffer_offset;
    progress = 0;
    read32(memory_target,endpoint_list_base()+endpoints[dir].entry_offset(),word);
    entry = word;
    if (entry.active === 1) return;
    buffer_offset = usb_ocp_base_epn_profile::ocp_get_buffer(
      dir ? USB_DIRECTION_IN : USB_DIRECTION_OUT);
    if (entry.active !== 0 || entry.nbytes !== 0 || entry.stall !== 0 ||
        entry.disabled !== 0 || entry.buffer_offset !==
          usb_ocp_base_epn_profile::ocp_get_retired_buffer_offset(
            dir ? USB_DIRECTION_IN : USB_DIRECTION_OUT,phase[dir]))
      `uvm_fatal("OCP_EPN_SERVICE", "Endpoint did not retire with exact short-packet writeback")
    data = usb_ocp_base_epn_profile::ocp_prepare_stream(
      dir ? USB_DIRECTION_IN : USB_DIRECTION_OUT,phase[dir]);
    if (dir == 0)
      for (int i = 0; i < data.size(); i += 4) begin
        read32(memory_target,buffer_offset+i,word);
        for (int j = 0; j < 4 && i+j < data.size(); j++)
          if (word[j*8+:8] !== data[i+j])
            `uvm_fatal("OCP_EPN_SERVICE", "Accepted OUT SRAM payload mismatch")
      end
    phase[dir]++;
    progress = 1;
    if (phase[dir] < 2) ocp_do_arm(dir);
  endtask

  task body();
    time deadline;
    bit progress;
    if (profile == null || !(device inside {1,2}) || profile.device != device)
      `uvm_fatal("OCP_EPN_SERVICE", "Invalid endpoint service ownership/profile")
    memory_target = (device == 1) ? USB_DEV0_SRAM : USB_DEV1_SRAM;
    deadline = $time + ocp_cfg.actor_timeout;
    while (ocp_cfg.epn_enabled[device-1] !== 1) begin
      if (ocp_cfg.stop_requested || $time >= deadline)
        `uvm_fatal("OCP_EPN_SERVICE", "Endpoint never legally enabled")
      #2us;
    end
    for (int dir = 0; dir < 2; dir++) begin
      endpoints[dir] = profile.ocp_prepare_endpoint(dir ? USB_DIRECTION_IN : USB_DIRECTION_OUT);
      ocp_do_arm(dir);
    end
    while (phase[0] < 2 || phase[1] < 2) begin
      if (ocp_cfg.stop_requested || $time >= deadline ||
          ocp_cfg.epn_enabled[device-1] !== 1)
        `uvm_fatal("OCP_EPN_SERVICE", "Unfinished EPN service or unexpected unconfiguration")
      for (int dir = 0; dir < 2; dir++)
        if (phase[dir] < 2) ocp_do_check_retirement(dir,progress);
      #2us;
    end
    ocp_cfg.epn_service_finished[device-1] = 1;
    completed = 1;
  endtask
endclass
