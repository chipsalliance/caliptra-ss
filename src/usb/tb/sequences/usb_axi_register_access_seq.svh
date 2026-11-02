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
// Setup-only stage of the AXI register-access scenario. Later stages add
// checked writes, B2B traffic, status preservation, and functional coverage.
class usb_axi_register_access_seq extends usb_base_seq;
  `uvm_object_utils(usb_axi_register_access_seq)

  localparam int unsigned DATA_WORD_COUNT = 5;

  uvm_reg data_regs[DATA_WORD_COUNT];
  uvm_reg recovery_control_reg;
  uvm_reg device_status_reg;
  uvm_reg protocol_cap_regs[2];
  uvm_reg dev1_route_reg;

  logic [31:0] data_offsets[DATA_WORD_COUNT];
  logic [31:0] recovery_control_offset;
  logic [31:0] device_status_offset;
  logic [31:0] protocol_cap_offsets[2];
  logic [31:0] dev1_route_offset;
  logic [31:0] image_select_mask;
  logic [31:0] activation_mask;
  logic [31:0] device_status_mask;
  logic [31:0] dev1_route_mask;

  logic [31:0] saved_recovery_control;
  logic [31:0] saved_device_status;
  logic [31:0] saved_protocol_caps[2];
  logic [31:0] saved_dev1_route;
  bit setup_completed;

  function new(string name = "usb_axi_register_access_seq");
    super.new(name);
  endfunction

  protected function logic [31:0] recovery_offset(uvm_reg register_handle);
    logic [31:0] offset;

    offset = reg_offset(USB_DEV0_CSR, register_handle);
    if (register_handle.get_n_bits() != USB_AXI_DATA_WIDTH ||
        offset[1:0] !== 2'b00 ||
        33'(offset) < usb_compound_pkg::RECOVERY_BASE_ADDR ||
        33'(offset) + 33'd4 > usb_compound_pkg::RECOVERY_ADDR_LIMIT) begin
      `uvm_fatal("USB_REGISTER_SETUP", $sformatf("Invalid recovery register %s at COMBO offset 0x%08h", register_handle.get_full_name(), offset))
    end
    return offset;
  endfunction

  protected function void resolve_registers();
    if (p_sequencer.reg_model.combo == null ||
        p_sequencer.reg_model.combo.recovery == null ||
        p_sequencer.reg_model.dev1_csr == null) begin
      `uvm_fatal("USB_REGISTER_SETUP", "Recovery or DEV1 CSR RAL block is missing")
    end
    data_regs[0] = p_sequencer.reg_model.combo.recovery.DEVICE_ID_1;
    data_regs[1] = p_sequencer.reg_model.combo.recovery.DEVICE_ID_2;
    data_regs[2] = p_sequencer.reg_model.combo.recovery.DEVICE_ID_3;
    data_regs[3] = p_sequencer.reg_model.combo.recovery.DEVICE_ID_4;
    data_regs[4] = p_sequencer.reg_model.combo.recovery.DEVICE_ID_5;
    recovery_control_reg = p_sequencer.reg_model.combo.recovery.RECOVERY_CTRL;
    device_status_reg = p_sequencer.reg_model.combo.recovery.DEVICE_STATUS_0;
    protocol_cap_regs[0] = p_sequencer.reg_model.combo.recovery.PROT_CAP_0;
    protocol_cap_regs[1] = p_sequencer.reg_model.combo.recovery.PROT_CAP_1;
    dev1_route_reg = p_sequencer.reg_model.dev1_csr.INTROUTE;

    foreach (data_regs[word]) begin
      data_offsets[word] = recovery_offset(data_regs[word]);
      if (data_offsets[word] != data_offsets[0] + 32'(word * 4)) begin
        `uvm_fatal("USB_REGISTER_SETUP", $sformatf("Recovery data register %s is not contiguous: offset=0x%08h first=0x%08h word=%0d", data_regs[word].get_full_name(), data_offsets[word], data_offsets[0], word))
      end
    end
    recovery_control_offset = recovery_offset(recovery_control_reg);
    device_status_offset = recovery_offset(device_status_reg);
    foreach (protocol_cap_regs[word]) begin
      protocol_cap_offsets[word] = recovery_offset(protocol_cap_regs[word]);
    end
    dev1_route_offset = reg_offset(USB_DEV1_CSR, dev1_route_reg);
    check_address(USB_DEV1_CSR, dev1_route_offset);

    image_select_mask = ral_field_mask(recovery_control_reg.get_field_by_name("REC_IMG_SEL"));
    activation_mask = ral_field_mask(recovery_control_reg.get_field_by_name("ACTIVATE_REC_IMG"));
    device_status_mask = ral_field_mask(device_status_reg.get_field_by_name("DEV_STATUS")) |
                         ral_field_mask(device_status_reg.get_field_by_name("PROT_ERROR")) |
                         ral_field_mask(device_status_reg.get_field_by_name("REC_REASON_CODE"));
    dev1_route_mask = USB_DEV1_ROUTE_MASK & (ral_field_mask(dev1_route_reg.get_field_by_name("EP_INT_ROUTE")) |
                                           ral_field_mask(dev1_route_reg.get_field_by_name("FRAME_INT_ROUTE")) |
                                           ral_field_mask(dev1_route_reg.get_field_by_name("DEV_INT_ROUTE")));
    `uvm_info("USB_REGISTER_SETUP", $sformatf("Resolved %0d data words at COMBO 0x%08h..0x%08h, control=0x%08h status=0x%08h DEV1 route=0x%08h; masks image=0x%08h activation=0x%08h status=0x%08h route=0x%08h", DATA_WORD_COUNT, data_offsets[0], data_offsets[DATA_WORD_COUNT - 1], recovery_control_offset, device_status_offset, dev1_route_offset, image_select_mask, activation_mask, device_status_mask, dev1_route_mask), UVM_LOW)
  endfunction

  protected task capture_snapshots();
    usb_axi_user_override user_override;

    user_override = usb_axi_user_override::with_value('0);
    ral_read32("RECOVERY_CTRL snapshot", recovery_control_reg, saved_recovery_control, user_override);
    ral_read32("DEVICE_STATUS_0 snapshot", device_status_reg, saved_device_status, user_override);
    foreach (protocol_cap_regs[word]) begin
      ral_read32($sformatf("PROT_CAP_%0d snapshot", word), protocol_cap_regs[word], saved_protocol_caps[word], user_override);
    end
    read32(USB_DEV1_CSR, dev1_route_offset, saved_dev1_route, user_override);
    if ($isunknown({saved_recovery_control, saved_device_status, saved_protocol_caps[0], saved_protocol_caps[1], saved_dev1_route})) begin
      `uvm_fatal("USB_REGISTER_SETUP", "Control/status snapshots contain unknown bits")
    end
    `uvm_info("USB_REGISTER_SETUP", $sformatf("Captured current-state snapshots: RECOVERY_CTRL=0x%08h DEVICE_STATUS_0=0x%08h PROT_CAP_0=0x%08h PROT_CAP_1=0x%08h DEV1_INTROUTE=0x%08h; no reset-value comparisons", saved_recovery_control, saved_device_status, saved_protocol_caps[0], saved_protocol_caps[1], saved_dev1_route), UVM_LOW)
  endtask

  task body();
    setup_completed = 1'b0;
    initialize_target_stats();
    check_axi_user_filters_bypassed();
    resolve_registers();
    capture_snapshots();
    setup_completed = 1'b1;
    `uvm_info("USB_REGISTER_SETUP", "Setup stage completed; write/B2B/status-preservation checks and AXI_001/004 functional coverage are not implemented yet", UVM_LOW)
  endtask
endclass
