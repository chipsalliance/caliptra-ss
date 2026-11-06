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

  // Register accesses and DMA reads are confined to combo.recovery.
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

  task ocp_poll_dma_ready(bit activation, time deadline, logic expected = 1'b1);
    bit ready;
    ready = 0;
    if (ocp_cfg.recovery_vif == null || $time >= deadline)
      `uvm_fatal("OCP_DMA", "Missing recovery interface or expired DMA deadline")
    fork
      begin
        fork
          begin
            wait ((activation ? ocp_cfg.recovery_vif.image_activated :
                                ocp_cfg.recovery_vif.payload_available) === expected);
            ready = 1;
          end
          begin #(deadline-$time); end
          begin wait (ocp_cfg.stop_requested === 1'b1); end
        join_any
        disable fork;
      end
    join
    if (!ready)
      `uvm_fatal("OCP_DMA", $sformatf("Architectural %s readiness timeout/teardown",
                                    activation ? "activation" : "payload"))
  endtask

  task ocp_do_check_dma_burst(int unsigned words);
    aaxi_master_tr request;
    logic [31:0] offset;
    offset = reg_offset(USB_DEV0_CSR,p_sequencer.reg_model.combo.recovery.INDIRECT_FIFO_DATA);
    if (words == 0 || words > 16)
      `uvm_fatal("OCP_DMA", "DMA requires 1..16 DWORD beats")
    request = create_transaction(USB_DEV0_CSR,offset,0,0);
    request.len = words-1;
    request.burst = AAXI_BURST_FIXED;
    execute_transaction(USB_DEV0_CSR,offset,0,request);
    if (request.rresp_Q.size() != words || request.data.size() != words*4)
      `uvm_fatal("OCP_DMA", "DMA burst returned wrong response/data count")
    foreach (request.rresp_Q[i])
      if (request.rresp_Q[i] !== AAXI_RESP_OKAY)
        `uvm_fatal("OCP_DMA", "DMA burst returned unsuccessful AXI response")
    // Every returned byte is independently reconciled by the passive checker.
    drained_words += words;
    `uvm_info("OCP_DMA",$sformatf("FIXED burst_words=%0d total_drained_words=%0d",
                                words,drained_words),UVM_LOW)
  endtask

  task body();
    logic [31:0] size_words;
    logic [31:0] control;
    logic [31:0] activation;
    time deadline;
    time poll_interval;
    int unsigned batch_words;
    int unsigned burst_words;
    ocp_write_register("CALIPTRA_CTRL",0);
    ocp_program_check_capabilities();
    ocp_write_register("RECOVERY_CTRL",0);
    ocp_read_register("RECOVERY_CTRL",activation);
    if (activation[23:16] !== 0)
      `uvm_fatal("OCP_CALIPTRA", "Activation zero baseline missing")
    if (ocp_cfg.recovery_vif == null ||
        ocp_cfg.recovery_vif.image_activated !== 1'b0 ||
        ocp_cfg.recovery_vif.payload_available !== 1'b0)
      `uvm_fatal("OCP_DMA", "Recovery attempt starts with stale/unknown DMA indications")
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
    if ($isunknown(size_words) || size_words > 1024)
      `uvm_fatal("OCP_CALIPTRA", "Image-size register exceeds bounded test envelope")
    ocp_read_register("INDIRECT_FIFO_CTRL_0",control);
    while (drained_words < size_words) begin
      if (ocp_cfg.stop_requested === 1'b1)
        `uvm_fatal("OCP_TEARDOWN", "Teardown before recovery image consumption")
      if ($time >= deadline) `uvm_fatal("OCP_CALIPTRA", "FIFO drain timeout")
      ocp_poll_dma_ready(0,deadline);
      batch_words = size_words-drained_words;
      if (batch_words > 64) batch_words = 64;
      while (batch_words != 0) begin
        burst_words = (batch_words > 16) ? 16 : batch_words;
        ocp_do_check_dma_burst(burst_words);
        batch_words -= burst_words;
      end
      // Do not authorize the next batch from the preceding publication level.
      ocp_poll_dma_ready(0,deadline,1'b0);
    end
    ocp_write_register("DEVICE_STATUS_0",
      (32'(OCP_REC_REASON_FORCED_RECOVERY)<<16) | OCP_DEVICE_STATUS_RECOVERY_PENDING);
    ocp_poll_dma_ready(1,deadline);
    ocp_read_register("RECOVERY_CTRL",activation);
    if ($time >= deadline) `uvm_fatal("OCP_CALIPTRA", "Fresh ACTIVATE register timeout")
    if (activation[23:16] !== OCP_RC_ACTIVATE_CODE ||
        activation[7:0] !== control[7:0] ||
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
