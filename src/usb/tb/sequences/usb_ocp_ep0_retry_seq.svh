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

class usb_ocp_ep0_retry_seq extends usb_ocp_bringup_seq;
  `uvm_object_utils(usb_ocp_ep0_retry_seq)
  usb_ocp_ep0_retry_host_seq host;

  function new(string name = "usb_ocp_ep0_retry_seq");
    super.new(name);
  endfunction

  virtual function usb_ocp_base_host_seq ocp_prepare_host();
    host = usb_ocp_ep0_retry_host_seq::type_id::create("host");
    return host;
  endfunction

  virtual function usb_ocp_base_mcu_seq ocp_prepare_mcu();
    usb_ocp_ep0_retry_mcu_seq mcu;
    mcu = usb_ocp_ep0_retry_mcu_seq::type_id::create("mcu");
    mcu.host = host;
    return mcu;
  endfunction

  virtual function usb_ocp_base_caliptra_seq ocp_prepare_caliptra();
    usb_ocp_ep0_retry_caliptra_seq caliptra;
    caliptra = usb_ocp_ep0_retry_caliptra_seq::type_id::create("caliptra");
    caliptra.host = host;
    return caliptra;
  endfunction

  task ocp_do_check_write_commit();
    logic [31:0] write_index;
    logic [31:0] initial_index;
    int unsigned expected_index;
    time deadline;
    wait (host != null && host.retry != null);
    if (!(host.mode inside {"both","write"}) || host.retry.skip_loss) return;
    wait (host.retry.original != null &&
          host.retry.kind == usb_ocp_ep0_retry_control::WRITE_RETRY && !host.status_probe);
    ral_read32("retry_initial_write_index",
      p_sequencer.reg_model.combo.recovery.INDIRECT_FIFO_STATUS_1,initial_index);
    if (host.retry.loss_applied || host.retry.data_acks != 0 || $isunknown(initial_index) ||
        (host.nak_mode != "out" && initial_index !== 0))
      `uvm_fatal("OCP_EP0_RETRY_BOUNDARY", "Missing unambiguous pre-acceptance public WRITE_INDEX")
    expected_index = host.retry.original.setup_data_w_length /
                     usb_ocp_ep0_retry_host_seq::DWORD_BYTES;
    if (expected_index == 0 || expected_index >= host.fifo_depth)
      `uvm_fatal("OCP_EP0_RETRY_BOUNDARY", "Selected chunk cannot qualify an unambiguous WRITE_INDEX advance")
    expected_index = (initial_index+expected_index)%host.fifo_depth;
    wait (host.retry.loss_applied);
    deadline = $time + usb_ocp_ep0_retry_host_seq::STATUS_OBSERVATION_TIMEOUT;
    // OCP 1.1 9.2 INDIRECT_FIFO_STATUS: Write Index counts accepted DWORDs.
    // An AXI read preserves the CONTROL transfer; a USB read would replace it.
    do begin
      ral_read32("retry_write_index",
        p_sequencer.reg_model.combo.recovery.INDIRECT_FIFO_STATUS_1,write_index);
      if (host.retry.ocp_post_loss_token_seen() || $time >= deadline)
        `uvm_fatal("OCP_EP0_RETRY_BOUNDARY", "Public write commit was not observed before repeated OUT")
      if (write_index === expected_index) break;
      #1us;
    end while (1);
    host.retry.write_committed_before_retry = 1;
    `uvm_info("OCP_EP0_RETRY_COMMIT", $sformatf(
      "Public WRITE_INDEX=%0d before repeated OUT; expected from original payload=%0d",
      write_index,expected_index), UVM_NONE)
  endtask

  task body();
    fork
      super.body();
      ocp_do_check_write_commit();
    join
  endtask
endclass
