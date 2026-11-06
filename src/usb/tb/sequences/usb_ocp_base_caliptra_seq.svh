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

class usb_ocp_base_caliptra_seq extends usb_ocp_base_seq;
  `uvm_object_utils(usb_ocp_base_caliptra_seq)
  localparam logic [15:0] UNSUPPORTED_PLATFORM_CAPS =
    (16'h1 << OCP_CAP_FORCED_RECOVERY) | (16'h1 << OCP_CAP_MGMT_RESET) |
    (16'h1 << OCP_CAP_DEVICE_RESET) | (16'h1 << OCP_CAP_INTERFACE_ISOLATION) |
    (16'h1 << OCP_CAP_FLASHLESS_BOOT);
  localparam logic [15:0] FIRMWARE_CAPS =
    (16'h1 << OCP_CAP_IDENTIFICATION) | (16'h1 << OCP_CAP_VENDOR);
  // OCP 1.1 9.2: UUID DEVICE_ID, no vendor string; firmware-owned identity.
  localparam logic [31:0] DEVICE_ID_WORDS[OCP_SPEC_MIN_LEN_DEVICE_ID/4] = '{
    {16'h1110,8'h00,OCP_DEVICE_ID_UUID}, 32'h15141312, 32'h19181716,
    32'h1d1c1b1a, 32'h00001f1e, 32'h00000000
  };
  localparam logic [31:0] VENDOR_DEFAULT_DATA = 32'h0000005a;
  int unsigned drained_words;

  function new(string name = "usb_ocp_base_caliptra_seq");
    super.new(name);
    drained_words = 0;
  endfunction

  // Every access is confined to combo.recovery and uses the existing bounded
  // RAL frontdoor API. No USB, phase, image-size, or payload handoff is used.
  task ocp_read_register(string name, output logic [31:0] data);
    uvm_reg r;
    r = p_sequencer.reg_model.combo.recovery.get_reg_by_name(name);
    ral_read32(name,r,data);
  endtask

  task ocp_write_register(string name, logic [31:0] data);
    uvm_reg r;
    r = p_sequencer.reg_model.combo.recovery.get_reg_by_name(name);
    ral_write32(name,r,data);
  endtask

  task ocp_program_check_capabilities();
    logic [31:0] capability_word;
    logic [31:0] readback;
    int unsigned capability_shift;
    string register_name;
    capability_shift = p_sequencer.reg_model.combo.recovery.PROT_CAP_2.
                       AGENT_CAPS_IDENTIFICATION.get_lsb_pos();
    ocp_read_register("PROT_CAP_2",capability_word);
    if ($isunknown(capability_word))
      `uvm_fatal("OCP_INIT", "Unknown PROT_CAP before firmware initialization")
    // Apply platform policy without advertising backing data before it exists.
    capability_word &= ~(32'(UNSUPPORTED_PLATFORM_CAPS | FIRMWARE_CAPS) << capability_shift);
    ocp_write_register("PROT_CAP_2",capability_word);
    foreach (DEVICE_ID_WORDS[i]) begin
      register_name = $sformatf("DEVICE_ID_%0d",i);
      ocp_write_register(register_name,DEVICE_ID_WORDS[i]);
      ocp_read_register(register_name,readback);
      if (readback !== DEVICE_ID_WORDS[i])
        `uvm_fatal("OCP_INIT", $sformatf("%s initialization readback mismatch",register_name))
    end
    ocp_write_register("VENDOR",VENDOR_DEFAULT_DATA);
    ocp_read_register("VENDOR",readback);
    if (readback !== VENDOR_DEFAULT_DATA)
      `uvm_fatal("OCP_INIT", "VENDOR initialization readback mismatch")
    capability_word |= 32'(FIRMWARE_CAPS) << capability_shift;
    ocp_write_register("PROT_CAP_2",capability_word);
    ocp_read_register("PROT_CAP_2",readback);
    if (readback !== capability_word)
      `uvm_fatal("OCP_INIT", "PROT_CAP capability-policy readback mismatch")
    `uvm_info("OCP_INIT",$sformatf(
      "Caliptra initialized DEVICE_ID/VENDOR and verified capabilities=0x%04h",
      readback >> capability_shift),UVM_LOW)
  endtask

  task body();
    logic [31:0] size_words;
    logic [31:0] control;
    logic [31:0] status;
    logic [31:0] data;
    logic [31:0] activation;
    time deadline;
    time service_gap;
    time poll_interval;
    ocp_write_register("CALIPTRA_CTRL",0);
    ocp_program_check_capabilities();
    ocp_write_register("RECOVERY_CTRL",0);
    ocp_read_register("RECOVERY_CTRL",activation);
    if (activation[23:16] !== 0)
      `uvm_fatal("OCP_CALIPTRA", "Activation zero baseline missing")
    ocp_write_register("DEVICE_STATUS_1",0);
    ocp_write_register("RECOVERY_STATUS",32'(OCP_RECOVERY_STATUS_AWAITING_IMAGE));
    ocp_write_register("DEVICE_STATUS_0",
      (32'(OCP_REC_REASON_FORCED_RECOVERY)<<16) | OCP_DEVICE_STATUS_RECOVERY_MODE);
    ocp_cfg.prepared[2] = 1;
    deadline = $time + ocp_cfg.actor_timeout;
    poll_interval = ocp_cfg.service_poll;
    do begin
      if (ocp_cfg.stop_requested === 1'b1)
        `uvm_fatal("OCP_TEARDOWN", "Teardown before recovery image consumption")
      if ($time >= deadline) `uvm_fatal("OCP_CALIPTRA", "Image-size register timeout")
      ocp_read_register("INDIRECT_FIFO_CTRL_1",size_words);
      if ($time >= deadline) `uvm_fatal("OCP_CALIPTRA", "Image-size register timeout")
      if (size_words !== 32'b0) break;
      ocp_wait_service_interval(poll_interval,deadline,"OCP_CALIPTRA","Image-size register timeout");
      poll_interval = ocp_get_next_idle_poll(poll_interval);
    end while (1);
    if ($isunknown(size_words) || size_words > 64)
      `uvm_fatal("OCP_CALIPTRA", "Unexpected small-image register size")
    ocp_read_register("INDIRECT_FIFO_CTRL_0",control);
    while (drained_words < size_words) begin
      if (ocp_cfg.stop_requested === 1'b1)
        `uvm_fatal("OCP_TEARDOWN", "Teardown before recovery image consumption")
      if ($time >= deadline) `uvm_fatal("OCP_CALIPTRA", "FIFO drain timeout")
      ocp_read_register("INDIRECT_FIFO_STATUS_0",status);
      if (status[0] === 1'b0) begin
        ocp_read_register("INDIRECT_FIFO_DATA",data);
        // The passive completed-AXI scoreboard checks each returned byte.
        drained_words++;
        service_gap = $urandom_range(0,int'(ocp_cfg.service_gap_max/1us))*1us;
        `uvm_info("OCP_SERVICE",$sformatf("drained_word=%0d gap=%0t",
                  drained_words,service_gap),UVM_MEDIUM)
        ocp_wait_service_interval(service_gap,deadline,"OCP_CALIPTRA","FIFO drain timeout");
      end else
        ocp_wait_service_interval(ocp_cfg.service_poll,deadline,"OCP_CALIPTRA","FIFO drain timeout");
    end
    ocp_write_register("DEVICE_STATUS_0",
      (32'(OCP_REC_REASON_FORCED_RECOVERY)<<16) | OCP_DEVICE_STATUS_RECOVERY_PENDING);
    do begin
      if (ocp_cfg.stop_requested === 1'b1)
        `uvm_fatal("OCP_TEARDOWN", "Teardown before fresh activation")
      if ($time >= deadline) `uvm_fatal("OCP_CALIPTRA", "Fresh ACTIVATE register timeout")
      ocp_read_register("RECOVERY_CTRL",activation);
      if ($time >= deadline) `uvm_fatal("OCP_CALIPTRA", "Fresh ACTIVATE register timeout")
      if (activation[23:16] === OCP_RC_ACTIVATE_CODE) break;
      ocp_wait_service_interval(ocp_cfg.service_poll,deadline,"OCP_CALIPTRA",
                                "Fresh ACTIVATE register timeout");
    end while (1);
    if (activation[7:0] !== control[7:0] ||
        activation[15:8] !== OCP_RC_IMAGE_SEL_CMS)
      `uvm_fatal("OCP_CALIPTRA", "Activation CMS/image selection mismatch")
    // This is emulated firmware status progression, not authentication or
    // execution of an image. Fresh AXI activation evidence precedes the clear.
    ocp_write_register("RECOVERY_CTRL",activation & 32'hff00ffff);
    ocp_write_register("RECOVERY_STATUS",32'(OCP_RECOVERY_STATUS_SUCCESS));
    ocp_write_register("DEVICE_STATUS_0",32'(OCP_DEVICE_STATUS_RUNNING_RECOVERY));
    completed = 1;
    ocp_poll_teardown();
    ocp_cfg.actor_finished[2] = 1;
  endtask
endclass
