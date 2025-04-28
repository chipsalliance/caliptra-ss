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

task mcu_trace_buffer_mon();
    forever begin
        @(posedge `MCI_PATH.i_mci_mcu_trace_buffer.clk or negedge cptra_rst_b);
        if (!cptra_rst_b) begin
            mcu_trace_buffer_wr_ptr <= 0;
            mcu_trace_buffer <= '{default: '0};
            mcu_trace_buffer_valid <= '0;
            mcu_trace_buffer_wrapped <= '0;
            trace_buffer_rd_ptr_f <= '0;
            trace_buffer_wr_ptr_f <= '0;
        end else begin
            if(`CPTRA_SS_TOP_PATH.mcu_trace_rv_i_valid_ip) begin
                mcu_trace_buffer_valid  <= 1;
                mcu_trace_buffer_wr_ptr <= (mcu_trace_buffer_wr_ptr + 4) % 256;
                mcu_trace_buffer[mcu_trace_buffer_wr_ptr]       <=    `CPTRA_SS_TOP_PATH.mcu_trace_rv_i_insn_ip;
                mcu_trace_buffer[mcu_trace_buffer_wr_ptr + 1]   <= `CPTRA_SS_TOP_PATH.mcu_trace_rv_i_address_ip;
                mcu_trace_buffer[mcu_trace_buffer_wr_ptr + 2]   <= `CPTRA_SS_TOP_PATH.mcu_trace_rv_i_tval_ip;
                mcu_trace_buffer[mcu_trace_buffer_wr_ptr + 3]   <= {
                                            21'h0,
                                            `CPTRA_SS_TOP_PATH.mcu_trace_rv_i_interrupt_ip, 
                                            `CPTRA_SS_TOP_PATH.mcu_trace_rv_i_ecause_ip,
                                            `CPTRA_SS_TOP_PATH.mcu_trace_rv_i_exception_ip};

                if ((mcu_trace_buffer_wr_ptr + 4) >= 256) begin
                    mcu_trace_buffer_wrapped <= 1'b1;
                end
            end
            //Flopped signals for assertions
            trace_buffer_wr_ptr_f <= `MCI_PATH.i_mci_mcu_trace_buffer.i_trace_buffer_csr.hwif_out.WRITE_PTR;
            trace_buffer_rd_ptr_f <= `MCI_PATH.i_mci_mcu_trace_buffer.i_trace_buffer_csr.hwif_out.READ_PTR;
        end
    end
endtask

// Verify when debug locked AXI reads return 0, writes are dropped and respond with error
`CALIPTRA_ASSERT(MCU_TRACE_BUFF_AXI_READ_WRITE_DEBUG_REJECT_A,
    `MCI_PATH.i_mci_mcu_trace_buffer.cif_resp_if.dv && `MCI_PATH.LCC_state_translator.security_state_o.debug_locked |->
    !`MCI_PATH.i_mci_mcu_trace_buffer.i_trace_buffer_csr.s_cpuif_req &&
    !`MCI_PATH.i_mci_mcu_trace_buffer.i_trace_buffer_csr.s_cpuif_req_is_wr &&
    `MCI_PATH.i_mci_mcu_trace_buffer.cif_resp_if.rdata === '0 &&
    `MCI_PATH.i_mci_mcu_trace_buffer.cif_resp_if.error,
    `MCI_PATH.i_mci_mcu_trace_buffer.clk, 
    !cptra_rst_b
);

// Verify all DMI reads return 0 when in not in debug mode
`CALIPTRA_ASSERT(MCU_TRACE_BUFF_DMI_READ_WRITE_DEBUG_REJECT_A,
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_en &&`MCI_PATH.LCC_state_translator.security_state_o.debug_locked |->
    !`MCI_PATH.i_mci_mcu_trace_buffer.dmi_wr_en_qual &&
    `MCI_PATH.i_mci_mcu_trace_buffer.dmi_reg === '0,
    `MCI_PATH.i_mci_mcu_trace_buffer.clk, 
    !cptra_rst_b
);

// Verify read to DATA register
`CALIPTRA_ASSERT(MCU_TRACE_BUFF_DMI_SUCC_READ_DATA_A,
    !`MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_wr_en && 
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_en && 
    !`MCI_PATH.LCC_state_translator.security_state_o.debug_locked  && 
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_addr === MCI_DMI_MCU_TRACE_DATA |-> ##1
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_rdata === mcu_trace_buffer[trace_buffer_rd_ptr_f],  
    `MCI_PATH.i_mci_mcu_trace_buffer.clk, 
    !cptra_rst_b
);


// Verify read to Status register
`CALIPTRA_ASSERT(MCU_TRACE_BUFF_DMI_SUCC_READ_STATUS_A,
    !`MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_wr_en && 
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_en && 
    !`MCI_PATH.LCC_state_translator.security_state_o.debug_locked  && 
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_addr === MCI_DMI_MCU_TRACE_STATUS |-> ##1
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_rdata[1:0] === {`MCI_PATH.i_mci_mcu_trace_buffer.i_trace_buffer_csr.hwif_out.STATUS.valid_data.value,`MCI_PATH.i_mci_mcu_trace_buffer.i_trace_buffer_csr.hwif_out.STATUS.wrapped.value}, 
    `MCI_PATH.i_mci_mcu_trace_buffer.clk, 
    !cptra_rst_b
);

// Verify DMI read to CONFIG file
`CALIPTRA_ASSERT(MCU_TRACE_BUFF_DMI_SUCC_READ_CONFIG_A,
    !`MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_wr_en && 
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_en && 
    !`MCI_PATH.LCC_state_translator.security_state_o.debug_locked  && 
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_addr === MCI_DMI_MCU_TRACE_CONFIG |-> ##1
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_rdata === `MCI_PATH.i_mci_mcu_trace_buffer.i_trace_buffer_csr.hwif_out.CONFIG.trace_buffer_depth.value, 
    `MCI_PATH.i_mci_mcu_trace_buffer.clk, 
    !cptra_rst_b
);

// Verify DMI read to WR_PTR
`CALIPTRA_ASSERT(MCU_TRACE_BUFF_DMI_SUCC_READ_WR_PTR_A,
    !`MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_wr_en && 
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_en && 
    !`MCI_PATH.LCC_state_translator.security_state_o.debug_locked  && 
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_addr === MCI_DMI_MCU_TRACE_WR_PTR |-> ##1
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_rdata === trace_buffer_wr_ptr_f, 
    `MCI_PATH.i_mci_mcu_trace_buffer.clk, 
    !cptra_rst_b
);

// Verify DMI read to RD_PTR register
`CALIPTRA_ASSERT(MCU_TRACE_BUFF_DMI_SUCC_READ_RD_PTR_A,
    !`MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_wr_en && 
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_en && 
    !`MCI_PATH.LCC_state_translator.security_state_o.debug_locked  && 
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_addr === MCI_DMI_MCU_TRACE_RD_PTR |-> ##1
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_rdata === trace_buffer_rd_ptr_f, 
    `MCI_PATH.i_mci_mcu_trace_buffer.clk, 
    !cptra_rst_b
);


logic [31:0] mcu_trace_buffer_capture_write_data;
always_ff @(posedge `MCI_PATH.i_mci_mcu_trace_buffer.clk or negedge cptra_rst_b) begin
    if (!cptra_rst_b) begin
        mcu_trace_buffer_capture_write_data <= 0;
    end else begin
        mcu_trace_buffer_capture_write_data <= `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_wdata;
    end
end

// Verify DMI write to DATA register
`CALIPTRA_ASSERT(MCU_TRACE_BUFF_DMI_SUCC_WRITE_RD_PTR_A,
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_wr_en && 
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_en && 
    !`MCI_PATH.LCC_state_translator.security_state_o.debug_locked  && 
    `MCI_PATH.i_mci_reg_top.mcu_dmi_uncore_addr === MCI_DMI_MCU_TRACE_RD_PTR |=>
    mcu_trace_buffer_capture_write_data === `MCI_PATH.i_mci_mcu_trace_buffer.i_trace_buffer_csr.hwif_out.READ_PTR, 
    `MCI_PATH.i_mci_mcu_trace_buffer.clk, 
    !cptra_rst_b
);


// Verify write pointer matches monitor
`CALIPTRA_ASSERT(MCU_TRACE_BUFF_WRITE_PTR_A,
    `CPTRA_SS_TOP_PATH.mcu_trace_rv_i_valid_ip |=> 
    (mcu_trace_buffer_wr_ptr === `MCI_PATH.i_mci_mcu_trace_buffer.trace_buffer_hwif_out.WRITE_PTR.ptr.value) && 
    (mcu_trace_buffer_wr_ptr === `MCI_PATH.i_mci_mcu_trace_buffer.dmi_reg_pre_security.TRACE_WR_PTR), 
    `MCI_PATH.i_mci_mcu_trace_buffer.clk, 
    !cptra_rst_b
);

// Verify Wrapped matches monitor
`CALIPTRA_ASSERT(MCU_TRACE_BUFF_WRAPPED_A,
    `CPTRA_SS_TOP_PATH.mcu_trace_rv_i_valid_ip |=> 
    (mcu_trace_buffer_wrapped === `MCI_PATH.i_mci_mcu_trace_buffer.trace_buffer_hwif_out.STATUS.wrapped) && 
    (mcu_trace_buffer_wrapped === `MCI_PATH.i_mci_mcu_trace_buffer.dmi_reg_pre_security.TRACE_STATUS[1]), 
    `MCI_PATH.i_mci_mcu_trace_buffer.clk, 
    !cptra_rst_b
);


// Verify Valid data matches monitor
`CALIPTRA_ASSERT(MCU_TRACE_BUFF_VALID_A,
    `CPTRA_SS_TOP_PATH.mcu_trace_rv_i_valid_ip |=> 
    (mcu_trace_buffer_valid === `MCI_PATH.i_mci_mcu_trace_buffer.trace_buffer_hwif_out.STATUS.valid_data) && 
    (mcu_trace_buffer_valid === `MCI_PATH.i_mci_mcu_trace_buffer.dmi_reg_pre_security.TRACE_STATUS[0]), 
    `MCI_PATH.i_mci_mcu_trace_buffer.clk, 
    !cptra_rst_b
);

// Verify Config matches monitor
`CALIPTRA_ASSERT(MCU_TRACE_BUFF_CONFIG_DEPTH_A,
    `CPTRA_SS_TOP_PATH.mcu_trace_rv_i_valid_ip |=> 
    (32'h100 === `MCI_PATH.i_mci_mcu_trace_buffer.trace_buffer_hwif_out.CONFIG.trace_buffer_depth.value) && 
    (32'h100 === `MCI_PATH.i_mci_mcu_trace_buffer.dmi_reg_pre_security.TRACE_CONFIG), 
    `MCI_PATH.i_mci_mcu_trace_buffer.clk, 
    !cptra_rst_b
);