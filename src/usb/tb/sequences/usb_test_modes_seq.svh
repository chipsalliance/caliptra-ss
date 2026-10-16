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

// Verifies the UTMI controls selected by TEST_J, TEST_K, and TEST_SE0_NAK.
class usb_test_modes_seq extends usb_base_seq;
  `uvm_object_utils(usb_test_modes_seq)

  localparam logic [2:0] TEST_J_MODE = 3'b001;
  localparam logic [2:0] TEST_K_MODE = 3'b010;
  localparam logic [2:0] TEST_SE0_NAK_MODE = 3'b011;
  localparam int unsigned STABLE_CYCLES = 16;

  bit completed;
  time mode_timeout = 20us;

  function new(string name = "usb_test_modes_seq");
    super.new(name);
  endfunction

  // Program PHY_TEST_MODE while preserving the live device status fields.
  task set_test_mode(logic [2:0] mode);
    logic [31:0] command;
    logic [31:0] mode_mask;
    logic [31:0] mode_value;

    mode_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.PHY_TEST_MODE);
    mode_value = ral_field_value(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.PHY_TEST_MODE, mode);
    ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    command = (command & ~mode_mask) | mode_value;
    ral_write32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    if ((command & mode_mask) !== mode_value) begin
      `uvm_fatal("USB_TEST_MODES", $sformatf("PHY_TEST_MODE readback is 0x%08h, expected selector %0d", command, mode))
    end
  endtask

  // Wait for and then continuously check one selector's UTMI control values.
  task check_mode_outputs(
    string label,
    logic [1:0] expected_opmode,
    logic expected_xcvrselect,
    logic expected_termselect,
    logic expected_txvalid,
    logic [7:0] expected_txdata
  );
    bit outputs_seen;

    outputs_seen = 1'b0;
    fork
      begin
        do begin
          @(posedge p_sequencer.usb_20_mac_if.utmi_dut_mac_if.CLK);
          outputs_seen = p_sequencer.ctrl_vif.utmi_opmode === expected_opmode &&
                         p_sequencer.ctrl_vif.utmi_xcvrselect === expected_xcvrselect &&
                         p_sequencer.ctrl_vif.utmi_termselect === expected_termselect &&
                         p_sequencer.ctrl_vif.utmi_txvalid === expected_txvalid &&
                         (!expected_txvalid || p_sequencer.ctrl_vif.utmi_txdata === expected_txdata);
        end while (!outputs_seen);
      end
      begin
        #(mode_timeout);
      end
    join_any
    disable fork;
    if (!outputs_seen) begin
      `uvm_fatal(
        "USB_TEST_MODES",
        $sformatf(
          "%s outputs did not appear within %0t: opmode=%b xcvr=%b term=%b txvalid=%b txdata=0x%02h",
          label,
          mode_timeout,
          p_sequencer.ctrl_vif.utmi_opmode,
          p_sequencer.ctrl_vif.utmi_xcvrselect,
          p_sequencer.ctrl_vif.utmi_termselect,
          p_sequencer.ctrl_vif.utmi_txvalid,
          p_sequencer.ctrl_vif.utmi_txdata
        )
      )
    end

    repeat (STABLE_CYCLES) begin
      @(posedge p_sequencer.usb_20_mac_if.utmi_dut_mac_if.CLK);
      if (p_sequencer.ctrl_vif.utmi_opmode !== expected_opmode ||
          p_sequencer.ctrl_vif.utmi_xcvrselect !== expected_xcvrselect ||
          p_sequencer.ctrl_vif.utmi_termselect !== expected_termselect ||
          p_sequencer.ctrl_vif.utmi_txvalid !== expected_txvalid ||
          (expected_txvalid && p_sequencer.ctrl_vif.utmi_txdata !== expected_txdata)) begin
        `uvm_fatal("USB_TEST_MODES", $sformatf("%s outputs changed during the %0d-cycle stability window", label, STABLE_CYCLES))
      end
    end
    `uvm_info("USB_TEST_MODES", $sformatf("%s UTMI controls remained stable for %0d PHY clocks", label, STABLE_CYCLES), UVM_LOW)
  endtask

  // Enumerate once, then exercise the remaining implemented test selectors.
  virtual task body();
    usb_init_seq init_sequence;

    completed = 1'b0;
    `uvm_info("USB_TEST_MODES", "Starting TEST_J/TEST_K/TEST_SE0_NAK scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_TEST_MODES", "Enumeration did not complete")
    end
    if (p_sequencer.ctrl_vif == null || p_sequencer.usb_20_mac_if == null) begin
      `uvm_fatal("USB_TEST_MODES", "Test-mode checking requires the USB control and UTMI interfaces")
    end

    `uvm_info("USB_TEST_MODES", "Selecting TEST_J (selector 1)", UVM_LOW)
    set_test_mode(TEST_J_MODE);
    check_mode_outputs("TEST_J", 2'b10, 1'b0, 1'b0, 1'b1, 8'hff);

    `uvm_info("USB_TEST_MODES", "Selecting TEST_K (selector 2)", UVM_LOW)
    set_test_mode(TEST_K_MODE);
    check_mode_outputs("TEST_K", 2'b10, 1'b0, 1'b0, 1'b1, 8'h00);

    `uvm_info("USB_TEST_MODES", "Selecting TEST_SE0_NAK (selector 3)", UVM_LOW)
    set_test_mode(TEST_SE0_NAK_MODE);
    check_mode_outputs("TEST_SE0_NAK", 2'b00, 1'b0, 1'b0, 1'b0, 8'h00);

    completed = 1'b1;
    `uvm_info("USB_TEST_MODES", "TEST_J, TEST_K, and TEST_SE0_NAK UTMI controls verified", UVM_LOW)
  endtask
endclass
