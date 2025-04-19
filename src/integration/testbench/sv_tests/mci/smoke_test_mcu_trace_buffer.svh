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


task smoke_test_mcu_trace_buffer();
    if($test$plusargs("MCU_TRACE_BUFFER_ONLY_ONE_ENTRY")) begin
        $display("[%s] Anly allowing a single trace entry in the trace buffer", $time);
        fork
            mcu_trace_buffer_force_num_entires(1); 
        join_none;
    end
    if($test$plusargs("MCU_TRACE_BUFFER_ONLY_64_ENTRY")) begin
        $display("[%s] Anly allowing a single trace entry in the trace buffer", $time);
        fork
            mcu_trace_buffer_force_num_entires(64); 
        join_none;
    end
    if($test$plusargs("MCU_TRACE_BUFFER_ONLY_63_ENTRY")) begin
        $display("[%s] Anly allowing a single trace entry in the trace buffer", $time);
        fork
            mcu_trace_buffer_force_num_entires(63); 
        join_none;
    end
    if($test$plusargs("MCU_TRACE_BUFFER_RANDOM_DATA")) begin
        $display("[%s] Randomly injecting trace data into the trace buffer", $time);
        fork
            mcu_trace_buffer_random_inject_trace_data();
        join_none;
    end

    wait_debug_unlock();

    halt_mcu_core(40000);


    if($test$plusargs("MCU_TRACE_BUFFER_ONLY_ONE_ENTRY")) begin
        bfm_axi_read_check(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_WRITE_PTR, $random(), 32'h4);
        bfm_axi_read_check(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_STATUS, $random(), `MCU_TRACE_BUFFER_CSR_STATUS_VALID_DATA_MASK);
    end
    if($test$plusargs("MCU_TRACE_BUFFER_ONLY_64_ENTRY")) begin
        bfm_axi_read_check(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_WRITE_PTR, $random(), 32'h0);
        bfm_axi_read_check(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_STATUS, $random(), (`MCU_TRACE_BUFFER_CSR_STATUS_VALID_DATA_MASK | `MCU_TRACE_BUFFER_CSR_STATUS_WRAPPED_MASK));
    end
    if($test$plusargs("MCU_TRACE_BUFFER_ONLY_63_ENTRY")) begin
        bfm_axi_read_check(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_WRITE_PTR, $random(), 32'd252);
        bfm_axi_read_check(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_STATUS, $random(), `MCU_TRACE_BUFFER_CSR_STATUS_VALID_DATA_MASK);
    end

    check_mcu_trace_buffer();


    end_test_successful_req();

endtask
