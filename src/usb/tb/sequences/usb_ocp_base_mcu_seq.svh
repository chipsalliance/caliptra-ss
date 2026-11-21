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

class usb_ocp_base_mcu_seq extends usb_ocp_firmware_base_seq;
  `uvm_object_utils(usb_ocp_base_mcu_seq)
  logic [31:0] hub_shadow;

  function new(string name = "usb_ocp_base_mcu_seq");
    super.new(name);
    device = 1;
  endfunction

  virtual task ocp_initialize_controller();
    logic [31:0] value;
    // Two-phase initialization follows usb.c usb_hub_init_and_connect().
    // Only the hub control register belongs here, never combo.recovery.
    ral_read32("HUB_CONTROL",p_sequencer.reg_model.combo.hub.CONTROL,value);
    hub_shadow = value & ral_field_mask(p_sequencer.reg_model.combo.hub.CONTROL.LPM_SUP);
    ral_write32("HUB_CONTROL",p_sequencer.reg_model.combo.hub.CONTROL,hub_shadow);
    // Test-owned unique hub VID/PID, while descriptor writes are unlocked.
    write32(USB_HUB,mem_word_offset(USB_HUB,
      p_sequencer.reg_model.combo.hub.DESCRIPTOR_LOW.m_mem,2),32'hca00_1209);
    hub_shadow |= ral_field_mask(p_sequencer.reg_model.combo.hub.CONTROL.ENABLE);
    ral_write32("HUB_ENABLE",p_sequencer.reg_model.combo.hub.CONTROL,hub_shadow);
    super.ocp_initialize_controller();
  endtask

  virtual task ocp_connect_upstream();
    bit ready;
    ready = 0;
    fork
      begin
        fork
          begin
            wait (ocp_cfg.prepared[0] && ocp_cfg.prepared[1] && ocp_cfg.prepared[2]);
            ready = 1;
          end
          begin #(ocp_cfg.actor_timeout); end
        join_any
        disable fork;
      end
    join
    if (!ready) `uvm_fatal("OCP_HUB", "Both downstream devices/recovery not prepared")
    hub_shadow |= ral_field_mask(p_sequencer.reg_model.combo.hub.CONTROL.DCON);
    ral_write32("HUB_CONNECT",p_sequencer.reg_model.combo.hub.CONTROL,hub_shadow);
  endtask
endclass
