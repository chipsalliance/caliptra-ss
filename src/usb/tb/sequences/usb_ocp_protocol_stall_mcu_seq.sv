// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_protocol_stall_mcu_seq extends usb_ocp_base_mcu_seq;
  `uvm_object_utils(usb_ocp_protocol_stall_mcu_seq)
  usb_ocp_protocol_stall_model stall_model;

  function new(string name = "usb_ocp_protocol_stall_mcu_seq");
    super.new(name);
  endfunction

  virtual task ocp_do_check_owned_setup(logic [7:0] request_type,
      logic [7:0] request, logic [15:0] value, logic [15:0] index,
      logic [15:0] length, output bit handled);
    logic [31:0] entry;
    logic [31:0] readback;
    usb_ep_entry_t decoded;
    time deadline;
    handled = 0;
    if (request_type !== 8'h02 || request !== svt_usb_types::CLEAR_FEATURE) return;
    if (device != 1 || stall_model == null || value !== 0 || index !== 0 || length !== 0)
      `uvm_fatal("OCP_STALL_FIRMWARE", "Only owned EP0 ENDPOINT_HALT clear is serviced")
    deadline = $time + ocp_cfg.control_transfer_timeout;
    while (!stall_model.ocp_check_clear_ready()) begin
      if ($time >= deadline)
        `uvm_fatal("OCP_STALL_FIRMWARE", "Firmware SETUP has no independently accepted legal CLEAR_FEATURE")
      #1us;
    end
    if (!stall_model.ocp_check_clear_service())
      `uvm_fatal("OCP_STALL_FIRMWARE", "CLEAR_FEATURE is not the first owned recovery request")
    // Programmer's Guide 4.2.2: S may be modified only with A=0.
    // Never skip a buffer, clear Active, reset the controller, or fake OCP.
    for (int offset = 0; offset <= 8; offset += 8) begin
      read32(memory_target,endpoint_list_base()+offset,entry);
      decoded = usb_ep_entry_t'(entry);
      if ($isunknown(entry))
        `uvm_fatal("OCP_STALL_FIRMWARE", "Unknown EP0 endpoint-list entry")
      if (decoded.active !== 0 && (decoded.stall === 1 || offset == 8))
        `uvm_fatal("OCP_STALL_FIRMWARE",
          "Legal CLEAR_FEATURE cannot modify/rearm an active EP0 buffer; STATUS and later recovery remain unreached")
      if (decoded.stall === 1) begin
        decoded.stall = 0;
        write32(memory_target,endpoint_list_base()+offset,32'(decoded));
        read32(memory_target,endpoint_list_base()+offset,readback);
        if (readback !== 32'(decoded))
          `uvm_error("OCP_STALL_FIRMWARE", "Frontdoor EP0 halt clear did not retain the other inactive entry fields")
      end
    end
    ocp_write_csr("INTSTAT",ocp_get_mask("INTSTAT","EP0IN"));
    // CLEAR_FEATURE is no-data/IN-STATUS. Leave an unhalted Active OUT entry
    // untouched; only the verified inactive IN entry needs STATUS rearming.
    write32(memory_target,endpoint_list_base()+8,
      endpoint_entry(1'b1,1'b0,0,IN_BUFFER));
    ocp_write_command(ocp_get_mask("DEVCMDSTAT","SETUP"));
    serviced++;
    stall_model.ocp_capture_firmware_clear();
    handled = 1;
  endtask
endclass
