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

class usb_ocp_ep0_retry_caliptra_seq extends usb_ocp_base_caliptra_seq;
  `uvm_object_utils(usb_ocp_ep0_retry_caliptra_seq)
  usb_ocp_ep0_retry_host_seq host;

  function new(string name = "usb_ocp_ep0_retry_caliptra_seq");
    super.new(name);
  endfunction

  virtual task ocp_do_check_dma_boundary();
    bit observed;
    if (host.nak_mode != "out" || drained_words != 0) return;
    ocp_poll_dma_ready(0,$time+ocp_cfg.control_transfer_timeout);
    observed = 0;
    // Architectural DMA scheduling holds the full FIFO, not private state.
    fork
      begin
        fork
          begin wait (host.retry.original != null && host.retry.naks != 0); observed = 1; end
          begin #(ocp_cfg.control_transfer_timeout); end
        join_any
        disable fork;
      end
    join
    if (!observed)
      `uvm_fatal("OCP_EP0_RETRY_NAK", "Full-FIFO DMA hold produced no selected native OUT NAK")
    `uvm_info("OCP_EP0_RETRY_NAK", "Observed full-FIFO OUT NAK; releasing normal DMA", UVM_NONE)
  endtask
endclass
