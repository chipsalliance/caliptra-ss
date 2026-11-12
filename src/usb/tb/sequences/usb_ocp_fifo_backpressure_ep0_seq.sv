// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_fifo_backpressure_ep0_seq extends usb_ocp_bringup_seq;
  `uvm_object_utils(usb_ocp_fifo_backpressure_ep0_seq)
  usb_ocp_fifo_backpressure_ep0_checker fifo_checker;

  function new(string name = "usb_ocp_fifo_backpressure_ep0_seq");
    super.new(name);
  endfunction

  virtual function usb_ocp_base_host_seq ocp_prepare_host();
    usb_ocp_fifo_backpressure_ep0_host_seq host;
    host = usb_ocp_fifo_backpressure_ep0_host_seq::type_id::create("host");
    host.fifo_checker = fifo_checker;
    return host;
  endfunction

  virtual function usb_ocp_base_caliptra_seq ocp_prepare_caliptra();
    usb_ocp_fifo_backpressure_ep0_caliptra_seq caliptra;
    caliptra = usb_ocp_fifo_backpressure_ep0_caliptra_seq::type_id::create("caliptra");
    caliptra.fifo_checker = fifo_checker;
    return caliptra;
  endfunction

  task body();
    usb_ocp_scoreboard scoreboard;
    uvm_reg_map memory_map;
    bit full;
    if (!uvm_config_db#(usb_ocp_scoreboard)::get(p_sequencer,"","ocp_scoreboard",scoreboard) ||
        !$cast(fifo_checker,scoreboard))
      `uvm_fatal("OCP_FIFO_EP0_GUARD", "FIFO EP0 testcase requires its owned passive checker")
    if (ocp_cfg.full_speed || scoreboard.l2_model != null || scoreboard.reset_model != null ||
        scoreboard.model.stall_model != null || scoreboard.model.require_dev0_ep0_replacement ||
        scoreboard.model.require_dev1_ep0_overlap || scoreboard.model.require_mixed_epn ||
        $test$plusargs("usb_ocp_control_zlp_canary") ||
        scoreboard.negative_replacement || scoreboard.negative_abort_prefix)
      `uvm_fatal("OCP_FIFO_EP0_GUARD", "FIFO EP0 row does not own FS/reset/L2/STALL/other overlap or replacement controls")
    foreach (ocp_cfg.epn_profiles[i])
      if (ocp_cfg.epn_profiles[i] != null)
        `uvm_fatal("OCP_FIFO_EP0_GUARD", "FIFO EP0 row must not configure EPN traffic")
    fifo_checker.ocp_cfg = ocp_cfg;
    fifo_checker.list_base = ocp_cfg.endpoint_list_base;
    memory_map = map_for(USB_DEV0_SRAM);
    fifo_checker.memory_base = memory_map.get_base_addr(UVM_NO_HIER);
    fifo_checker.setup_clear_mask =
      ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.SETUP);
    scoreboard.model.require_dev0_ep0_replacement = 1;
    // A non-destructive bounded capacity witness reports a short-capacity
    // hang without resetting, draining, or discarding already accepted data.
    full = 0;
    fork
      begin super.body(); end
      begin
        wait (fifo_checker.experiment_armed);
        fork
          begin wait (fifo_checker.full_status_seen); full = 1; end
          begin #4ms; end
        join_any
        disable fork;
        if (!full)
          `uvm_fatal("OCP_FIFO_EP0_WAIT", $sformatf(
            "Advertised-capacity/full-status witness timeout: capacity_words=%0d accepted=%0d returned=%0d full_prefix=%0b hold=%0b; blocked/replacement/resubmission/final recovery remain unreached",
            fifo_checker.model.fifo_depth_words,fifo_checker.model.accepted_bytes,
            fifo_checker.model.returned_bytes,fifo_checker.full_prefix_seen,
            fifo_checker.dma_hold_entered))
      end
    join
  endtask
endclass
