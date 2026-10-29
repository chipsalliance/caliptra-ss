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
// smoke_test_mcu_trace_buffer_cptra_core
//
// Verifies that the MCI trace buffer collects the CALIPTRA CORE trace stream when
// the source select (trace_buffer_csr.CTRL.cptra_core_sel) is set to 1. Leverages
// the existing MCU trace-buffer verification infrastructure: the source-aware golden
// model in mci_mcu_trace_buffer_mon.svh follows CTRL.cptra_core_sel and captures
// cptra_trace_rv_i_* when selected, so check_mcu_trace_buffer() compares the read-back
// buffer against the Caliptra-core trace.
//
// Note: trace COLLECTION is not gated by debug; only READ access is. Debug is unlocked
// here so the buffer can be read back over the SoC AXI fabric.
//
// Sequence (race-conscious):
//   1. Wait for debug unlock (trace-buffer CSR read access is debug-gated).
//   2. Select the Caliptra core as the trace source via a SoC-side AXI write to CTRL.
//      Once selected, only Caliptra-core trace is captured (the mux ignores MCU trace).
//   3. Halt the MCU (not the captured source once selected; keeps the system quiet).
//   4. Wait for the write pointer to traverse one full buffer AFTER the source select,
//      so every entry is Caliptra-core trace.
//   5. Freeze the Caliptra-core trace valid so the buffer is stable for the multi-cycle
//      read-back and golden compare.
//   6. Check STATUS (valid_data + wrapped) and every entry against the golden model.
//
// NOTE: the wait/freeze timing and the companion's trace production may need tuning
// during simulation bring-up; validate against the simulator.

task smoke_test_mcu_trace_buffer_cptra_core();
    logic [31:0] wr_ptr_start;

    $display("[%t] Starting smoke test for MCU Trace Buffer - Caliptra core source", $time);

    wait_debug_unlock();

    // Select the Caliptra core as the trace-buffer source. After this, only
    // Caliptra-core trace is captured.
    $display("[%t] Selecting Caliptra core as trace source (CTRL.cptra_core_sel=1)", $time);
    bfm_axi_write_single(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_CTRL, $urandom(),
                         `MCU_TRACE_BUFFER_CSR_CTRL_CPTRA_CORE_SEL_MASK);

    // Quiet the MCU (not the captured source once selected).
    halt_mcu_core(40000);

    // Wait for one full buffer of Caliptra-core trace captured AFTER the source
    // select: the write pointer must leave its current value and return to it (a full
    // wrap), guaranteeing every entry is Caliptra-core trace.
    @(posedge `MCI_PATH.i_mci_mcu_trace_buffer.clk);
    wr_ptr_start = mcu_trace_buffer_wr_ptr;
    $display("[%t] Waiting for a full buffer of Caliptra-core trace (wr_ptr wrap from 0x%0h)", $time, wr_ptr_start);
    wait (mcu_trace_buffer_wr_ptr !== wr_ptr_start);
    wait (mcu_trace_buffer_wr_ptr === wr_ptr_start);

    // Freeze the Caliptra-core trace stream for a stable read-back and golden compare.
    force `CPTRA_SS_TOP_PATH.cptra_trace_rv_i_valid_ip = '0;

    // The buffer must report valid data and wrapped, and every entry must match the
    // source-aware golden model (which followed CTRL.cptra_core_sel).
    bfm_axi_read_check(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_STATUS, $urandom(),
                       (`MCU_TRACE_BUFFER_CSR_STATUS_VALID_DATA_MASK | `MCU_TRACE_BUFFER_CSR_STATUS_WRAPPED_MASK));

    check_mcu_trace_buffer();

    release `CPTRA_SS_TOP_PATH.cptra_trace_rv_i_valid_ip;

    end_test_successful_req();

endtask
