// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_fifo_backpressure_epn_caliptra_seq extends usb_ocp_base_caliptra_seq;
  `uvm_object_utils(usb_ocp_fifo_backpressure_epn_caliptra_seq)
  usb_ocp_fifo_backpressure_epn_checker fifo_checker;

  function new(string name = "usb_ocp_fifo_backpressure_epn_caliptra_seq");
    super.new(name);
  endfunction

  virtual task ocp_do_check_dma_boundary();
    bit released;
    if (fifo_checker == null)
      `uvm_fatal("OCP_FIFO_EPN_GUARD", "Missing owned first-DMA barrier")
    if (drained_words != 0 || fifo_checker.dma_released) return;
    // Readiness is an architectural DUT input to this actor, not a flag
    // synthesized by the host. Hold before the first unchanged DMA operation.
    ocp_poll_dma_ready(0,$time+ocp_cfg.control_transfer_timeout);
    fifo_checker.dma_hold_entered = 1;
    released = 0;
    `uvm_info("OCP_FIFO_EPN_HOLD", "Payload available; entered planned first-DMA hold",UVM_NONE)
    fork
      begin
        fork
          begin wait (fifo_checker.dma_released); released = 1; end
          begin #(2*ocp_cfg.control_transfer_timeout); end
          begin wait (ocp_cfg.stop_requested === 1'b1); end
        join_any
        disable fork;
      end
    join
    if (!released)
      `uvm_fatal("OCP_FIFO_EPN_WAIT",$sformatf(
        "First-DMA hold timeout/teardown: capacity=%0b full=%0b blocked=%0b EPN=%0b consumed=%0b; no reset/drain escape",
        fifo_checker.full_prefix_seen,fifo_checker.full_status_seen,
        fifo_checker.blocked_seen,fifo_checker.overlap_joined,fifo_checker.proof_consumed))
    // Inherited fixed-address 16-DWORD bursts, four per 256-byte batch,
    // and exact shorter final burst remain unmodified.
  endtask
endclass
