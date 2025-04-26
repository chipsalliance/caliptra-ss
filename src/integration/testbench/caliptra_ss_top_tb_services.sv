// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
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

`default_nettype none

`include "css_mcu0_common_defines.vh"
`include "config_defines.svh"
`include "caliptra_reg_defines.svh"
`include "caliptra_macros.svh"
`include "i3c_defines.svh"
`include "soc_address_map_defines.svh"
`include "caliptra_ss_includes.svh"


module caliptra_ss_top_tb_services
import css_mcu0_el2_pkg::*;
import tb_top_pkg::*; 
#(
  parameter UVM_TB = 0,
  `include "css_mcu0_el2_param.vh"
) (
  input  logic                       clk,
  input  logic                       rst_l,
  input  int                         cycleCnt,
  input logic                        cptra_ss_rdc_clk_cg_o,
  caliptra_ss_bfm_services_if.tb_services soc_bfm_if,
  css_mcu0_el2_mem_if                cptra_ss_mcu0_el2_mem_export,
  mci_mcu_sram_if                    cptra_ss_mci_mcu_sram_req_if,
  mci_mcu_sram_if                    cptra_ss_mcu_mbox0_sram_req_if,
  mci_mcu_sram_if                    cptra_ss_mcu_mbox1_sram_req_if,
  axi_mem_if                         mcu_rom_mem_export_if
);

    `include "caliptra_ss_tb_cmd_list.svh"

    int                         commit_count;

    bit          [31:0]         mem_signature_begin = 32'd0; // TODO:
    bit          [31:0]         mem_signature_end   = 32'd0;

    logic                       mailbox_data_val;
    logic                       mailbox_write;
    logic        [63:0]         mailbox_data;
    logic        [63:0]         prev_mailbox_data;


    logic                       cold_rst;
    logic                       warm_rst;
    logic                       clr_cold_rst;
    logic                       clr_warm_rst;

    string                      abi_reg[32]; // ABI register names

    tb_top_pkg::veer_sram_error_injection_mode_t error_injection_mode;
    tb_top_pkg::mcu_mbox_sram_error_injection_mode_t mbox0_sram_error_injection_mode;
    tb_top_pkg::mcu_mbox_sram_error_injection_mode_t mbox1_sram_error_injection_mode;
    tb_top_pkg::mcu_mbox_sram_error_injection_mode_t mcu_sram_error_injection_mode;
    
    bit                         flip_bit_mbox0;
    bit                         flip_bit_mbox1;
    logic [MCU_MBOX0_DATA_AND_ECC_W-1:0] mbox0_sram_wdata_bitflip;
    logic [MCU_MBOX1_DATA_AND_ECC_W-1:0] mbox1_sram_wdata_bitflip;
    
    bit                         flip_bit_mcu_sram;
    logic [MCU_SRAM_DATA_TOTAL_WIDTH-1:0] mcu_sram_wdata_bitflip;

    logic                       wb_valid;
    logic [4:0]                 wb_dest;
    logic [31:0]                wb_data;
    logic                       wb_csr_valid;
    logic [11:0]                wb_csr_dest;
    logic [31:0]                wb_csr_data;

    time i3c_run_time;

    // Instantiate the fuse controller / lifecycle testbench services submodule
    fc_lcc_tb_services u_fc_lcc_tb_services (
        .clk                    (clk),
        .cptra_rst_b            (rst_l),
        .tb_service_cmd_valid   (mailbox_write),
        .tb_service_cmd         (mailbox_data[7:0])
    );

    logic [$bits(lc_ctrl_state_pkg::lc_state_t)-1:0] MANUF_state;
    logic [$bits(lc_ctrl_state_pkg::lc_state_t)-1:0] PROD_state;
    assign MANUF_state = lc_ctrl_state_pkg::lc_state_t'(lc_ctrl_state_pkg::LcStDev);
    assign PROD_state = lc_ctrl_state_pkg::lc_state_t'(lc_ctrl_state_pkg::LcStProd);
    initial begin
        if ($test$plusargs("CALIPTRA_SS_UDS_PROG") || $test$plusargs("CALIPTRA_SS_MANUF_DBG") || $test$plusargs("CALIPTRA_SS_PROD_DBG")) begin
            $monitor("CALIPTRA_SS_UDS_PROG: UDS_REQ is %x\n",`CPTRA_SS_TOP_PATH.caliptra_top_dut.soc_ifc_top1.soc_ifc_reg_hwif_out.SS_DBG_MANUF_SERVICE_REG_REQ.UDS_PROGRAM_REQ.value);
            $monitor("CALIPTRA_SS_UDS_PROG: UDS_RESP IN PROGRESS is %x\n",`CPTRA_SS_TOP_PATH.caliptra_top_dut.soc_ifc_top1.soc_ifc_reg_hwif_out.SS_DBG_MANUF_SERVICE_REG_RSP.UDS_PROGRAM_IN_PROGRESS);
            $monitor("CALIPTRA_SS_UDS_PROG: UDS_RESP UDS_PROGRAM_FAIL is %x\n",`CPTRA_SS_TOP_PATH.caliptra_top_dut.soc_ifc_top1.soc_ifc_reg_hwif_out.SS_DBG_MANUF_SERVICE_REG_RSP.UDS_PROGRAM_FAIL);
            $monitor("CALIPTRA_SS_UDS_PROG: UDS_RESP UDS_PROGRAM_SUCCESS is %x\n",`CPTRA_SS_TOP_PATH.caliptra_top_dut.soc_ifc_top1.soc_ifc_reg_hwif_out.SS_DBG_MANUF_SERVICE_REG_RSP.UDS_PROGRAM_SUCCESS);
            $monitor("CALIPTRA_SS_UDS_PROG: BootFSM_GO is %x\n",`CPTRA_SS_TOP_PATH.caliptra_top_dut.soc_ifc_top1.soc_ifc_reg_hwif_out.CPTRA_BOOTFSM_GO);
            $monitor("CALIPTRA_SS_UDS_PROG: BootFSM_BrkPoint_Latched is %x\n",`CPTRA_SS_TOP_PATH.caliptra_top_dut.soc_ifc_top1.BootFSM_BrkPoint_Latched);
            $monitor("CALIPTRA_SS_UDS_PROG: CPTRA_FLOW_STATUS is %x\n",`CPTRA_SS_TOP_PATH.caliptra_top_dut.soc_ifc_top1.soc_ifc_reg_hwif_in.CPTRA_FLOW_STATUS);
            // force `CPTRA_SS_TB_TOP_NAME.cptra_ss_cptra_core_m_axi_if.awuser = CPTRA_SS_STRAP_CLPTRA_CORE_AXI_USER;
            force `CPTRA_SS_TB_TOP_NAME.cptra_ss_cptra_core_bootfsm_bp_i = 1'b1;
            force `CPTRA_CORE_TOP_PATH.soc_ifc_top1.soc_ifc_reg_hwif_in.CPTRA_HW_CONFIG.SUBSYSTEM_MODE_en.next = 1'b1;
        end
        if ($test$plusargs("CALIPTRA_SS_UDS_PROG")) begin
            force `MCI_PATH.from_otp_to_lcc_program_i.state = MANUF_state;
        end
        if ($test$plusargs("CALIPTRA_SS_MANUF_DBG")) begin
            force `MCI_PATH.from_otp_to_lcc_program_i.state = MANUF_state;
            force `CPTRA_CORE_TOP_PATH.soc_ifc_top1.timer1_timeout_period = 64'hFFFFFFFF_FFFFFFFF;
            force `CPTRA_SS_TB_TOP_NAME.cptra_ss_debug_intent_i = 1'b1;
        end 
        if ($test$plusargs("CALIPTRA_SS_PROD_DBG")) begin
            force `MCI_PATH.from_otp_to_lcc_program_i.state = PROD_state;
            force `CPTRA_CORE_TOP_PATH.soc_ifc_top1.timer1_timeout_period = 64'hFFFFFFFF_FFFFFFFF;
            force `CPTRA_SS_TB_TOP_NAME.cptra_ss_debug_intent_i = 1'b1;
        end 
        if ($test$plusargs("CALIPTRA_SS_JTAG_DBG")) begin
            force `MCI_PATH.from_otp_to_lcc_program_i.state = MANUF_state;
            force `MCI_PATH.ss_dbg_manuf_enable_i = 1'b1;
        end 
        if ($test$plusargs("CALIPTRA_SS_JTAG_MCI_BRK")) begin
            force `MCI_PATH.from_otp_to_lcc_program_i.state = PROD_state;
            force `CPTRA_SS_TB_TOP_NAME.cptra_ss_debug_intent_i = 1'b1;
            force `CPTRA_SS_TB_TOP_NAME.cptra_ss_mci_boot_seq_brkpoint_i = 1'b1;
        end 
    end

    assign mailbox_write    = `MCI_PATH.i_mci_reg_top.i_mci_reg.field_combo.DEBUG_OUT.DATA.load_next && rst_l;
    assign mailbox_data     = `MCI_PATH.i_mci_reg_top.i_mci_reg.field_combo.DEBUG_OUT.DATA.next;

    assign mailbox_data_val = mailbox_data[7:0] > 8'h5 && mailbox_data[7:0] < 8'h7f;

    int    hex_file_is_empty;

    integer fd, tp, el;

    always @(negedge clk or negedge rst_l) begin
        if(!rst_l) begin
            prev_mailbox_data <= 'hA; // Initialize with newline character so timestamp is printed to console for the first line
        end
        else begin
            if( mailbox_data_val & mailbox_write) begin
                prev_mailbox_data <= mailbox_data;
            end
        end

    end

    //Note update these as more errors are added to aggregate_error bus
    int rand_err_injection_sel;
    localparam NUM_AGG_ERROR_FATAL = 6;
    localparam NUM_AGG_ERROR_NON_FATAL = 6;
    localparam NUM_NOTIF0_INTR = 13; //Exclude generic_input_wires

    always @(negedge clk) begin
        // console Monitor
        if( mailbox_data_val & mailbox_write) begin
            if (prev_mailbox_data[7:0] inside {8'h0A,8'h0D}) begin
                $fwrite(fd,"%0t - ", $time);
                $write("%0t - ", $time);
            end
            $fwrite(fd,"%c", mailbox_data[7:0]);
            $write("%c", mailbox_data[7:0]);
            if (mailbox_data[7:0] inside {8'h0A,8'h0D}) begin // CR/LF
                $fflush(fd);
            end
        end
        // ECC error injection
        if(mailbox_write && (mailbox_data[7:0] == TB_CMD_INJECT_ECC_ERROR_SINGLE_DCCM)) begin
            $display("Injecting single bit DCCM error");
            error_injection_mode.dccm_single_bit_error <= 1'b1;
        end
        else if(mailbox_write && (mailbox_data[7:0] == TB_CMD_INJECT_ECC_ERROR_DOUBLE_DCCM)) begin
            $display("Injecting double bit DCCM error");
            error_injection_mode.dccm_double_bit_error <= 1'b1;
        end
        else if(mailbox_write && (mailbox_data[7:0] == TB_CMD_DISABLE_INJECT_ECC_ERROR)) begin
            $display("Disable ECC error injection");
            error_injection_mode <= '0;
        end
        // ECC error injection - FIXME
        error_injection_mode.dccm_single_bit_error <= 1'b0;
        error_injection_mode.dccm_double_bit_error <= 1'b0;

        //TODO: randomly select which error bit to force for more complete testing
        // MCI error injection
        if (mailbox_write && (mailbox_data[7:0] == TB_CMD_INJECT_MCI_ERROR_FATAL)) begin
            $display("Injecting MCI errs");
            
            force `MCI_REG_TOP_PATH.nmi_intr = 1'b1;
            @(negedge clk);
            release `MCI_REG_TOP_PATH.nmi_intr;
            repeat($urandom_range(0,15)) @(negedge clk);
        
            force `MCI_REG_TOP_PATH.mcu_sram_double_ecc_error = 1'b1;
            @(negedge clk);
            release `MCI_REG_TOP_PATH.mcu_sram_double_ecc_error;
            repeat($urandom_range(0,15)) @(negedge clk);
        
            force `MCI_REG_TOP_PATH.mcu_sram_dmi_axi_collision_error = 1'b1;
            @(negedge clk);
            release `MCI_REG_TOP_PATH.mcu_sram_dmi_axi_collision_error;
        end

        //MCI non-fatal error injection
        if (mailbox_write && (mailbox_data[7:0] == TB_CMD_INJECT_MCI_ERROR_NON_FATAL)) begin
            $display("Injecting non-ftl MCI errs");

            force `MCI_REG_TOP_PATH.mbox0_sram_double_ecc_error = 1'b1;
            @(negedge clk);
            release `MCI_REG_TOP_PATH.mbox0_sram_double_ecc_error;
            repeat($urandom_range(0,15)) @(negedge clk);

            force `MCI_REG_TOP_PATH.mbox1_sram_double_ecc_error = 1'b1;
            @(negedge clk);
            release `MCI_REG_TOP_PATH.mbox1_sram_double_ecc_error;
        end

        //Aggregate fatal error injection
        if (mailbox_write && (mailbox_data[7:0] == TB_CMD_INJECT_AGG_ERROR_FATAL)) begin
            $display("Injecting random aggregate ftl err");
            rand_err_injection_sel = $urandom_range(0,NUM_AGG_ERROR_FATAL-1);

            case(rand_err_injection_sel)
                0: begin
                    force `CPTRA_SS_TOP_PATH.cptra_error_fatal = 1'b1;
                    @(negedge clk);
                    release `CPTRA_SS_TOP_PATH.cptra_error_fatal;
                end
                1: begin
                    force `CPTRA_SS_TOP_PATH.mcu_dccm_ecc_double_error = 1'b1;
                    @(negedge clk);
                    release `CPTRA_SS_TOP_PATH.mcu_dccm_ecc_double_error;
                end
                2: begin
                    force `CPTRA_SS_TOP_PATH.lc_alerts_o = $urandom_range(1,(2**lc_ctrl_reg_pkg::NumAlerts)-1);
                    @(negedge clk);
                    release `CPTRA_SS_TOP_PATH.lc_alerts_o;
                end
                3: begin
                    force `CPTRA_SS_TOP_PATH.fc_alerts = $urandom_range(1, (2**otp_ctrl_reg_pkg::NumAlerts)-1);
                    @(negedge clk);
                    release `CPTRA_SS_TOP_PATH.fc_alerts;
                end
                4: begin
                    force `CPTRA_SS_TOP_PATH.i3c_peripheral_reset = 1'b1;
                    @(negedge clk);
                    release `CPTRA_SS_TOP_PATH.i3c_peripheral_reset;
                end
                5: begin
                    force `CPTRA_SS_TOP_PATH.i3c_escalated_reset = 1'b1;
                    @(negedge clk);
                    release `CPTRA_SS_TOP_PATH.i3c_escalated_reset;
                end
                default: begin
                end
            endcase
        end

        //Aggregate non_fatal error injection
        if (mailbox_write && (mailbox_data[7:0] == TB_CMD_INJECT_AGG_ERROR_NON_FATAL)) begin
            $display("Injecting random aggregate non ftl err");
            rand_err_injection_sel = $urandom_range(0,NUM_AGG_ERROR_NON_FATAL-1);

            case(rand_err_injection_sel)
                0: begin
                    force `CPTRA_SS_TOP_PATH.cptra_error_non_fatal = 1'b1;
                    @(negedge clk);
                    release `CPTRA_SS_TOP_PATH.cptra_error_non_fatal;
                end
                1: begin
                    force `CPTRA_SS_TOP_PATH.mcu_dccm_ecc_single_error = 1'b1;
                    @(negedge clk);
                    release `CPTRA_SS_TOP_PATH.mcu_dccm_ecc_single_error;
                end
                2: begin
                    force `CPTRA_SS_TOP_PATH.lc_alerts_o = $urandom_range(1,(2**lc_ctrl_reg_pkg::NumAlerts)-1);
                    @(negedge clk);
                    release `CPTRA_SS_TOP_PATH.lc_alerts_o;
                end
                3: begin
                    force `CPTRA_SS_TOP_PATH.fc_alerts = $urandom_range(1, (2**otp_ctrl_reg_pkg::NumAlerts)-1);
                    @(negedge clk);
                    release `CPTRA_SS_TOP_PATH.fc_alerts;
                end
                4: begin
                    force `CPTRA_SS_TOP_PATH.i3c_peripheral_reset = 1'b1;
                    @(negedge clk);
                    release `CPTRA_SS_TOP_PATH.i3c_peripheral_reset;
                end
                5: begin
                    force `CPTRA_SS_TOP_PATH.i3c_escalated_reset = 1'b1;
                    @(negedge clk);
                    release `CPTRA_SS_TOP_PATH.i3c_escalated_reset;
                end
                default: begin
                end
            endcase
        end

        if (mailbox_write && (mailbox_data[7:0] == TB_CMD_INJECT_NOTIF0)) begin
            $display("Injecting random notif0 condition");
            rand_err_injection_sel = $urandom_range(0,NUM_NOTIF0_INTR-1);

            case(rand_err_injection_sel)
                0: begin
                    force `MCI_REG_TOP_PATH.mcu_sram_single_ecc_error = 1'b1;
                    @(negedge clk);
                    release `MCI_REG_TOP_PATH.mcu_sram_single_ecc_error;
                end
                1: begin
                    force `MCI_REG_TOP_PATH.cptra_mcu_rst_req = 1'b1;
                    @(negedge clk);
                    release `MCI_REG_TOP_PATH.cptra_mcu_rst_req;
                end
                2: begin
                    force `MCI_REG_TOP_PATH.mcu_mbox0_target_user_done = 1'b1;
                    @(negedge clk);
                    release `MCI_REG_TOP_PATH.mcu_mbox0_target_user_done;
                end
                3: begin
                    force `MCI_REG_TOP_PATH.mcu_mbox1_target_user_done = 1'b1;
                    @(negedge clk);
                    release `MCI_REG_TOP_PATH.mcu_mbox1_target_user_done;
                end
                4: begin
                    force `MCI_REG_TOP_PATH.mcu_mbox0_data_avail = 1'b1;
                    @(negedge clk);
                    release `MCI_REG_TOP_PATH.mcu_mbox0_data_avail;
                end
                5: begin
                    force `MCI_REG_TOP_PATH.mcu_mbox1_data_avail = 1'b1;
                    @(negedge clk);
                    release `MCI_REG_TOP_PATH.mcu_mbox1_data_avail;
                end
                6: begin
                    force `MCI_REG_TOP_PATH.cptra_mbox_data_avail = 1'b1;
                    @(negedge clk);
                    release `MCI_REG_TOP_PATH.cptra_mbox_data_avail;
                end
                7: begin
                    force `MCI_REG_TOP_PATH.mbox0_sram_single_ecc_error = 1'b1;
                    @(negedge clk);
                    release `MCI_REG_TOP_PATH.mbox0_sram_single_ecc_error;
                end
                8: begin
                    force `MCI_REG_TOP_PATH.mbox1_sram_single_ecc_error = 1'b1;
                    @(negedge clk);
                    release `MCI_REG_TOP_PATH.mbox1_sram_single_ecc_error;
                end
                9: begin
                    force `MCI_REG_TOP_PATH.security_state_o.debug_locked = 1'b1;
                    @(negedge clk);
                    release `MCI_REG_TOP_PATH.security_state_o.debug_locked;
                end
                10: begin
                    force `MCI_REG_TOP_PATH.scan_mode = 1'b1;
                    @(negedge clk);
                    release `MCI_REG_TOP_PATH.scan_mode;
                end
                11: begin
                    force `MCI_REG_TOP_PATH.soc_req_mbox0_lock = 1'b1;
                    @(negedge clk);
                    release `MCI_REG_TOP_PATH.soc_req_mbox0_lock;
                end
                12: begin
                    force `MCI_REG_TOP_PATH.soc_req_mbox1_lock = 1'b1;
                    @(negedge clk);
                    release `MCI_REG_TOP_PATH.soc_req_mbox1_lock;
                end
                default: begin
                end
            endcase
        end

        // Disable MCU_SRAM assertions
        if(mailbox_write && (mailbox_data[7:0] == TB_DISABLE_MCU_SRAM_PROT_ASSERTS)) begin
            $assertoff(0, `MCI_PATH.i_mci_mcu_sram_ctrl.ERR_MCU_SRAM_PROT_REGION_FILTER_ERROR);
        end
        // Memory signature dump and test END
        if((mailbox_write && (mailbox_data[7:0] == TB_CMD_END_SIM_WITH_SUCCESS || mailbox_data[7:0] == TB_CMD_END_SIM_WITH_FAILURE)) || soc_bfm_if.end_test_success) begin
            if (mem_signature_begin < mem_signature_end) begin
                dump_signature();
            end
            // End Of test monitor
            else if(mailbox_data[7:0] == TB_CMD_END_SIM_WITH_SUCCESS || soc_bfm_if.end_test_success ) begin
                if(`MCU_PATH.rst_l) begin
                    $display("Halting MCU");
                    force `MCI_PATH.mcu_cpu_halt_req_o = 1;
                    $display("Waiting for MCU to halt");
                    wait(`MCI_PATH.mcu_cpu_halt_ack_i);
                    $display("Waiting for MCU halt status");
                    wait(`MCI_PATH.mcu_cpu_halt_status_i);
                end

                $display("* TESTCASE PASSED");
                $display("\nFinished : minstret = %0d, mcycle = %0d", `MCU_DEC.tlu.minstretl[31:0],`MCU_DEC.tlu.mcyclel[31:0]);
                $display("See \"mcu_exec.log\" for execution trace with register updates..\n");
                if($test$plusargs("AVY_TEST")) begin
                    if($value$plusargs("i3c_run_time=%0d", i3c_run_time)) begin
                        $display("Waiting %0t for I3C tests to finish..\n", i3c_run_time);
                        #i3c_run_time;
                    end else begin
                        i3c_run_time = 500us;
                        $display("Waiting %0t for I3C tests to finish..\n", i3c_run_time);
                        #i3c_run_time;
                    end
                end
                $finish;
            end
            else if(mailbox_data[7:0] == TB_CMD_END_SIM_WITH_FAILURE) begin
                $error("* TESTCASE FAILED");
                $finish;
            end
        end
    end

    // Aids debugging with waves
    logic [7:0] isr_active = 8'h0;
    always @(negedge clk) begin
        if ((mailbox_data[7:0] == TB_CMD_DECR_INTR_ACTIVE) && mailbox_write) begin
            isr_active--;
        end
        else if ((mailbox_data[7:0] == TB_CMD_INCR_INTR_ACTIVE) && mailbox_write) begin
            isr_active++;
        end
    end

    always @(negedge clk or negedge rst_l) begin
        if (!rst_l) begin
            mbox0_sram_error_injection_mode <= '{default: 1'b0};
            mbox1_sram_error_injection_mode <= '{default: 1'b0};
        end
        else if(mailbox_write && (mailbox_data[7:0] == TB_CMD_INJECT_MBOX_SRAM_SINGLE_ECC_ERROR)) begin
            $display("Injecting single bit MCU Mbox SRAM errors");
            mbox0_sram_error_injection_mode.single_bit_error <= 1'b1;
            mbox1_sram_error_injection_mode.single_bit_error <= 1'b1;
        end
        else if(mailbox_write && (mailbox_data[7:0] == TB_CMD_INJECT_MBOX_SRAM_DOUBLE_ECC_ERROR)) begin
            $display("Injecting double bit MCU Mbox SRAM errors");
            mbox0_sram_error_injection_mode.double_bit_error <= 1'b1;
            mbox1_sram_error_injection_mode.double_bit_error <= 1'b1;
        end
        else if(mailbox_write && (mailbox_data[7:0] == TB_CMD_RANDOMIZE_MBOX_SRAM_ECC_ERROR_INJECTION)) begin
            $display("Randomizing MCU SRAM Mbox error injection");
            mbox0_sram_error_injection_mode.randomize <= 1'b1;
            mbox1_sram_error_injection_mode.randomize <= 1'b1;
        end
        else if(mailbox_write && (mailbox_data[7:0] == TB_CMD_DISABLE_MBOX_SRAM_ECC_ERROR_INJECTION)) begin
            $display("Disabling MCU SRAM Mbox injection");
            mbox0_sram_error_injection_mode <= '{default: 1'b0};
            mbox1_sram_error_injection_mode <= '{default: 1'b0};
        end
    end


    always @(negedge clk or negedge rst_l) begin
        if (!rst_l) begin
            mcu_sram_error_injection_mode <= '{default: 1'b0};
        end
        else if(mailbox_write && (mailbox_data[7:0] == TB_CMD_INJECT_MCU_SRAM_SINGLE_ECC_ERROR)) begin
            $display("Injecting single bit MCU SRAM errors");
            mcu_sram_error_injection_mode.single_bit_error <= 1'b1;
            $assertoff(0, `MCI_PATH.i_mci_mcu_sram_ctrl.ERR_MCU_SRAM_ECC_SB_ERROR);

        end
        else if(mailbox_write && (mailbox_data[7:0] == TB_CMD_INJECT_MCU_SRAM_DOUBLE_ECC_ERROR)) begin
            $display("Injecting double bit MCU SRAM errors");
            mcu_sram_error_injection_mode.double_bit_error <= 1'b1;
            $assertoff(0, `MCI_PATH.i_mci_mcu_sram_ctrl.ERR_MCU_SRAM_ECC_DB_ERROR);
        end
        else if(mailbox_write && (mailbox_data[7:0] == TB_CMD_RANDOMIZE_MCU_SRAM_ECC_ERROR_INJECTION)) begin
            $display("Randomizing MCU SRAM error injection");
            mcu_sram_error_injection_mode.randomize <= 1'b1;
            $assertoff(0, `MCI_PATH.i_mci_mcu_sram_ctrl.ERR_MCU_SRAM_ECC_SB_ERROR);
            $assertoff(0, `MCI_PATH.i_mci_mcu_sram_ctrl.ERR_MCU_SRAM_ECC_DB_ERROR);
        end
        else if(mailbox_write && (mailbox_data[7:0] == TB_CMD_DISABLE_MCU_SRAM_ECC_ERROR_INJECTION)) begin
            $display("Disabling MCU SRAM injection");
            mcu_sram_error_injection_mode <= '{default: 1'b0};
        end
    end

    // Load SHA Test Vectors into MCU SRAM
    initial begin
        bit sha512_mode;
        bit[MCU_SRAM_ECC_WIDTH-1:0] ecc;
        bit[MCU_SRAM_DATA_WIDTH-1:0] data;
        bit[MCU_SRAM_ADDR_WIDTH-1:0] addr;
        int signed ii;
        int fd_r;
        int cnt_tmp = 0;
        int line_skip;
        int test_case;

        string line_read;
        string tmp_str1;
        string tmp_str2;
        string file_name;
        int most_sig_dword;
        reg [3199:0][31:0] sha_block_data;
        reg [31:0] block_len;
        reg [15:0][31:0] sha_digest;
        reg [31:0] dlen;
        reg [1:0] byte_shift;
        forever begin
            @(negedge clk);
            if(mailbox_write && (mailbox_data[7:0] == TB_CMD_SHA_VECTOR_TO_MCU_SRAM)) begin
                // ============= SHA test setup =============
                // Randomize test parameters
                if (!std::randomize(sha512_mode)) $fatal("Failed to randomize sha mode");
                if (!std::randomize(test_case) with {test_case inside {[1:256]};}) $fatal("Failed to randomize test_case");
                if (sha512_mode) begin
                    case(test_case) inside
                    [0:128]: begin
                      file_name = "./SHA512ShortMsg.rsp";
                      line_skip = test_case * 4 + 7;
                    end
                    [129:256]: begin
                      file_name = "./SHA512LongMsg.rsp";
                      line_skip = (test_case - 129) * 4 + 7;
                    end
                  endcase
                end
                else begin
                    case(test_case) inside
                    [0:128]: begin
                        file_name = "./SHA384ShortMsg.rsp";
                        line_skip = test_case * 4 + 7;
                    end
                    [129:256]: begin
                      file_name = "./SHA384LongMsg.rsp";
                      line_skip = (test_case - 129) * 4 + 7;
                    end
                  endcase
                end
                $display("[%t] TB: Populating SHA testcase (mode=%s, case=%d, fname=%s) to MCU SRAM", $time, sha512_mode?"SHA512":"SHA384", test_case, file_name);

                // Parse appropriate test vector files
                fd_r = $fopen(file_name,"r");

                while (cnt_tmp <= line_skip) begin
                    cnt_tmp = cnt_tmp + 1;
                    void'($fgets(line_read,fd_r));
                end

                void'($sscanf( line_read, "%s %s %d", tmp_str1, tmp_str2, block_len));
                void'($fgets(line_read,fd_r));
                void'($sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, sha_block_data));
                void'($fgets(line_read,fd_r));
                void'($sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, sha_digest));
                
                $fclose(fd_r);

                dlen = block_len >> 3; // in bytes
                byte_shift = 'd4 - dlen[1:0];
                sha_block_data = sha_block_data << (byte_shift * 8);

                // ============= SHA test load to SRAM =============
                // Set mode to dw0
                data = MCU_SRAM_DATA_WIDTH'(sha512_mode);
                ecc = |data ? riscv_ecc32(data) : 0;
                lmem.ram[0] = {ecc,data};
                // Set length (in bytes) to dw1
                data = MCU_SRAM_DATA_WIDTH'(dlen);
                ecc = |data ? riscv_ecc32(data) : 0;
                lmem.ram[1] = {ecc,data};
                // Set expected digest at byte offset 'h100 = dw offset 'h40
                addr = 'h40;
                for (ii=0; ii < (sha512_mode ? 16 : 12); ii++) begin
                    data = sha_digest[(sha512_mode ? 16 : 12) - 1 - ii];
                    $display("TB: [SHA Digest Iteration: %0d] Setting SRAM offset 0x%x with dword: 0x%x", ii, addr, data);
                    ecc = |data ? riscv_ecc32(data) : 0;
                    lmem.ram[addr] = {ecc,data};
                    addr += 1; // Dword address
                end

                // Set message starting at byte offset 'h400 = dw offset 'h100
                addr = 'h100;

                //Divide the number of bytes by 4 to get the number of dwords.
                //If the data is evenly divisible, the most significant dword is N-1. If it includes a partial dword it's already rounded down
                most_sig_dword = (dlen[1:0] == 2'b00) ? (dlen >> 2) - 1 : (dlen >> 2);

                if (dlen != 0) begin
                    for (ii=most_sig_dword; ii >= 0 ; ii--) begin
                        data = sha_block_data[ii];
                        $display("TB: [SHA Message Iteration: %0d] Setting SRAM offset 0x%x with dword: 0x%x", ii, addr, data);
                        ecc = |data ? riscv_ecc32(data) : 0;
                        lmem.ram[addr] = {ecc,data};
                        addr += 1; // Dword address
                    end
                end
            end
        end
    end

///////////////////////////////////////////////
// Time controls 
//////////////////////////////////////////////

///////////////////////////////////////////////
// Reset controls
//////////////////////////////////////////////

    always@(negedge clk) begin
        if((mailbox_data[7:0] == TB_CMD_COLD_RESET) && mailbox_write) begin 
            $display("[%t] COLD RESET REQUESTED", $time);
            cold_rst <= 1'b1; 
            warm_rst <= 1'b0;
        end
        else if((mailbox_data[7:0] == TB_CMD_WARM_RESET) && mailbox_write) begin
            $display("[%t] WARM RESET REQUESTED", $time);
            warm_rst <= 1'b1;
            cold_rst <= 1'b0;
        end
        else if(clr_cold_rst) begin
            cold_rst <= 1'b0;
        end
        else if(clr_warm_rst) begin
            warm_rst <= 1'b0;
        end

    end

initial begin
    soc_bfm_if.deassert_hard_rst_flag = 1'b0;
    soc_bfm_if.deassert_rst_flag      = 1'b0;
    soc_bfm_if.assert_hard_rst_flag   = 1'b0;
    soc_bfm_if.assert_rst_flag        = 1'b0;
    clr_cold_rst                      = 1'b0;
    clr_warm_rst                      = 1'b0;

    forever begin
        @(posedge clk);
        if(cold_rst) begin
            @(posedge clk);
            $display("[%t] COLD RESET: Powergood Reset asserting", $time);
            soc_bfm_if.assert_hard_rst_flag <= 1'b1;
            clr_cold_rst               <= 1'b1;
            @(posedge clk);
            clr_cold_rst               <= 1'b0;
            soc_bfm_if.assert_hard_rst_flag <= 1'b0;
            wait(soc_bfm_if.assert_hard_rst_flag_done);
            $display("[%t] COLD RESET: Hold", $time);
            repeat(20) begin
                @(posedge clk);
            end
            $display("[%t] COLD RESET: Powergood Reset deasserting", $time);
            soc_bfm_if.deassert_hard_rst_flag <= 1'b1;
            @(posedge clk);
            soc_bfm_if.deassert_hard_rst_flag <= 1'b0;
            wait(soc_bfm_if.deassert_hard_rst_flag_done);

            $display("[%t] COLD RESET: COMPLETE", $time);
        end
        else if(warm_rst) begin
            @(posedge clk);
            $display("[%t] WARM RESET: Resets asserting", $time);
            soc_bfm_if.assert_rst_flag <= 1'b1;
            clr_warm_rst               <= 1'b1;
            @(posedge clk);
            soc_bfm_if.assert_rst_flag <= 1'b0;
            clr_warm_rst               <= 1'b0;
            wait(soc_bfm_if.assert_rst_flag_done);
            $display("[%t] WARM RESET: Hold", $time);
            repeat(10) begin
                @(posedge clk);
            end
            $display("[%t] WARM RESET: Resets deasserting", $time);
            soc_bfm_if.deassert_rst_flag <= 1'b1;
            @(posedge clk);
            soc_bfm_if.deassert_rst_flag <= 1'b0;
            wait(soc_bfm_if.deassert_rst_flag_done);
            $display("[%t] WARM RESET: COMPLETE", $time);
        end
    end
end



    // trace monitor
    always @(posedge clk) begin
        wb_valid      <= `MCU_DEC.dec_i0_wen_r;
        wb_dest       <= `MCU_DEC.dec_i0_waddr_r;
        wb_data       <= `MCU_DEC.dec_i0_wdata_r;
        wb_csr_valid  <= `MCU_DEC.dec_csr_wen_r;
        wb_csr_dest   <= `MCU_DEC.dec_csr_wraddr_r;
        wb_csr_data   <= `MCU_DEC.dec_csr_wrdata_r;
        if (`MCU_PATH.trace_rv_i_valid_ip) begin
           $fwrite(tp,"%b,%h,%h,%0h,%0h,3,%b,%h,%h,%b\n", `MCU_PATH.trace_rv_i_valid_ip, 0, `MCU_PATH.trace_rv_i_address_ip,
                  0, `MCU_PATH.trace_rv_i_insn_ip,`MCU_PATH.trace_rv_i_exception_ip,`MCU_PATH.trace_rv_i_ecause_ip,
                  `MCU_PATH.trace_rv_i_tval_ip,`MCU_PATH.trace_rv_i_interrupt_ip);
           // Basic trace - no exception register updates
           // #1 0 ee000000 b0201073 c 0b02       00000000
           commit_count++;
           $fwrite (el, "%10d : %8s 0 %h %h%13s %14s ; %s\n", cycleCnt, $sformatf("#%0d",commit_count),
                        `MCU_PATH.trace_rv_i_address_ip, `MCU_PATH.trace_rv_i_insn_ip,
                        (wb_dest !=0 && wb_valid)?  $sformatf("%s=%h", abi_reg[wb_dest], wb_data) : "            ",
                        (wb_csr_valid)? $sformatf("c%h=%h", wb_csr_dest, wb_csr_data) : "             ",
                        dasm(`MCU_PATH.trace_rv_i_insn_ip, `MCU_PATH.trace_rv_i_address_ip, wb_dest & {5{wb_valid}}, wb_data)
                   );
        end
        if(`MCU_DEC.dec_nonblock_load_wen) begin
            $fwrite (el, "%10d : %32s=%h                ; nbL\n", cycleCnt, abi_reg[`MCU_DEC.dec_nonblock_load_waddr], `MCU_DEC.lsu_nonblock_load_data);
            `CPTRA_SS_TB_TOP_NAME.u_caliptra_ss_top_tb_services.gpr[0][`MCU_DEC.dec_nonblock_load_waddr] = `MCU_DEC.lsu_nonblock_load_data;
        end
        if(`MCU_DEC.exu_div_wren) begin
            $fwrite (el, "%10d : %32s=%h                ; nbD\n", cycleCnt, abi_reg[`MCU_DEC.div_waddr_wb], `MCU_DEC.exu_div_result);
            `CPTRA_SS_TB_TOP_NAME.u_caliptra_ss_top_tb_services.gpr[0][`MCU_DEC.div_waddr_wb] = `MCU_DEC.exu_div_result;
        end
    end


    initial begin
        abi_reg[0] = "zero";
        abi_reg[1] = "ra";
        abi_reg[2] = "sp";
        abi_reg[3] = "gp";
        abi_reg[4] = "tp";
        abi_reg[5] = "t0";
        abi_reg[6] = "t1";
        abi_reg[7] = "t2";
        abi_reg[8] = "s0";
        abi_reg[9] = "s1";
        abi_reg[10] = "a0";
        abi_reg[11] = "a1";
        abi_reg[12] = "a2";
        abi_reg[13] = "a3";
        abi_reg[14] = "a4";
        abi_reg[15] = "a5";
        abi_reg[16] = "a6";
        abi_reg[17] = "a7";
        abi_reg[18] = "s2";
        abi_reg[19] = "s3";
        abi_reg[20] = "s4";
        abi_reg[21] = "s5";
        abi_reg[22] = "s6";
        abi_reg[23] = "s7";
        abi_reg[24] = "s8";
        abi_reg[25] = "s9";
        abi_reg[26] = "s10";
        abi_reg[27] = "s11";
        abi_reg[28] = "t3";
        abi_reg[29] = "t4";
        abi_reg[30] = "t5";
        abi_reg[31] = "t6";

        lmem_dummy_preloader.ram = '{default:8'h0};
        hex_file_is_empty = $system("test -s mcu_lmem.hex");
        if (!hex_file_is_empty) $readmemh("mcu_lmem.hex",lmem_dummy_preloader.ram, 0, (MCU_SRAM_SIZE_KB*1024)-1);

        imem.ram = '{default:8'h0};
        $readmemh("mcu_program.hex",  imem.ram);

        tp = $fopen("mcu_trace_port.csv","w");
        el = $fopen("mcu_exec.log","w");
        $fwrite (el, "//   Cycle : #inst    0    pc    opcode    reg=value    csr=value     ; mnemonic\n");
        fd = $fopen("mcu_console.log","w");
        commit_count = 0;

        css_mcu0_dummy_dccm_preloader.ram = '{default:8'h0};
        hex_file_is_empty = $system("test -s mcu_dccm.hex");
        if (!hex_file_is_empty) $readmemh("mcu_dccm.hex",css_mcu0_dummy_dccm_preloader.ram,0,32'h0001_FFFF);

        // preload_dccm();
        preload_css_mcu0_dccm();
        preload_mcu_sram();

    end


    // Mbox0 SRAM error injection
    `ifndef VERILATOR
        initial begin
            automatic bitflip_mask_generator #(MCU_MBOX0_DATA_AND_ECC_W) bitflip_gen = new();
            forever begin
                @(posedge clk)
                if (~|mbox0_sram_error_injection_mode) begin
                    mbox0_sram_wdata_bitflip <= '0;
                end
                else if (cptra_ss_mcu_mbox0_sram_req_if.req.cs & cptra_ss_mcu_mbox0_sram_req_if.req.we) begin
                    // Corrupt 20% of the writes if randomize is enabled
                    flip_bit_mbox0 = (mbox0_sram_error_injection_mode.randomize) ? ($urandom_range(0,99) < 20) : 1'b1;
                    mbox0_sram_wdata_bitflip <= flip_bit_mbox0 ? bitflip_gen.get_mask(mbox0_sram_error_injection_mode.double_bit_error) : '0;
                    if (flip_bit_mbox0) begin
                    //    $display("%t Injecting bit flips to Mbox0 SRAM[%d] Bitflip Mask: 0x%x Write Data: 0x%x", 
                    //                             $realtime, cptra_ss_mcu_mbox0_sram_req_if.req.addr >>2, mbox0_sram_wdata_bitflip, cptra_ss_mcu_mbox0_sram_req_if.req.wdata);
                    end
                end
            end
        end
    `else
        always @(posedge clk) begin
            if (~|mbox0_sram_error_injection_mode) begin
                flip_bit_mbox0 <= 0;
                mbox0_sram_wdata_bitflip <= '0;
            end
            else if (cptra_ss_mcu_mbox0_sram_req_if.req.cs & cptra_ss_mcu_mbox0_sram_req_if.req.cs) begin
                // Corrupt 20% of the writes if randomize is enabled
                flip_bit_mbox0 = (mbox0_sram_error_injection_mode.randomize) ? ($urandom_range(0,99) < 20) : 1'b1;
                mbox0_sram_wdata_bitflip <= flip_bit_mbox0 ? get_bitflip_mask(mbox0_sram_error_injection_mode.double_bit_error) : '0;
            end
        end
    `endif

    // Mbox1 SRAM error injection
    `ifndef VERILATOR
        initial begin
            automatic bitflip_mask_generator #(MCU_MBOX1_DATA_AND_ECC_W) bitflip_gen = new();
            forever begin
                @(posedge clk)
                if (~|mbox1_sram_error_injection_mode) begin
                    mbox1_sram_wdata_bitflip <= '0;
                end
                else if (cptra_ss_mcu_mbox1_sram_req_if.req.cs & cptra_ss_mcu_mbox1_sram_req_if.req.we) begin
                    flip_bit_mbox1 = (mbox1_sram_error_injection_mode.randomize) ? ($urandom_range(0,99) < 20) : 1'b1;
                    mbox1_sram_wdata_bitflip <= flip_bit_mbox1 ? bitflip_gen.get_mask(mbox1_sram_error_injection_mode.double_bit_error) : '0;
                    // if (flip_bit_mbox1) $display("Injecting bit flips to Mbox1 SRAM[%d]", $realtime, mbox1_sram_wdata_bitflip, cptra_ss_mcu_mbox1_sram_req_if.req.addr >>2);
                end
            end
    end
    `else
        always @(posedge clk) begin
            if (~|mbox1_sram_error_injection_mode) begin
                flip_bit_mbox1 <= 0;
                mbox1_sram_wdata_bitflip <= '0;
            end
            else if (cptra_ss_mcu_mbox1_sram_req_if.req.cs & cptra_ss_mcu_mbox1_sram_req_if.req.cs) begin
                // Corrupt 20% of the writes if randomize is enabled
                flip_bit_mbox1 = (mbox1_sram_error_injection_mode.randomize) ? ($urandom_range(0,99) < 20) : 1'b1;
                mbox1_sram_wdata_bitflip <= flip_bit_mbox1 ? get_bitflip_mask(mbox1_sram_error_injection_mode.double_bit_error) : '0;
            end
        end
    `endif

    // MCU SRAM error injection
    `ifndef VERILATOR
        initial begin
            automatic bitflip_mask_generator #(MCU_SRAM_DATA_TOTAL_WIDTH) bitflip_gen = new();
            forever begin
                @(posedge clk)
                if (~|mcu_sram_error_injection_mode) begin
                    mcu_sram_wdata_bitflip <= '0;
                end
                else if (cptra_ss_mci_mcu_sram_req_if.req.cs & cptra_ss_mci_mcu_sram_req_if.req.we) begin
                    // Corrupt 20% of the writes if randomize is enabled
                    flip_bit_mcu_sram = (mcu_sram_error_injection_mode.randomize) ? ($urandom_range(0,99) < 20) : 1'b1;
                    mcu_sram_wdata_bitflip <= flip_bit_mcu_sram ? bitflip_gen.get_mask(mcu_sram_error_injection_mode.double_bit_error) : '0;
                    if (flip_bit_mcu_sram) begin
                    //    $display("%t Injecting bit flips to MCU SRAM[%d] Bitflip Mask: 0x%x Write Data: 0x%x", 
                    //                             $realtime, cptra_ss_mci_mcu_sram_req_if.req.addr >>2, mcu_sram_wdata_bitflip, cptra_ss_mci_mcu_sram_req_if.req.wdata);
                    end
                end
            end
        end
    `else
        always @(posedge clk) begin
            if (~|mcu_sram_error_injection_mode) begin
                flip_bit_mcu_sram <= 0;
                mcu_sram_wdata_bitflip <= '0;
            end
            else if (cptra_ss_mci_mcu_sram_req_if.req.cs & cptra_ss_mci_mcu_sram_req_if.req.cs) begin
                // Corrupt 20% of the writes if randomize is enabled
                flip_bit_mcu_sram = (mcu_sram_error_injection_mode.randomize) ? ($urandom_range(0,99) < 20) : 1'b1;
                mcu_sram_wdata_bitflip <= flip_bit_mcu_sram ? get_bitflip_mask(mcu_sram_error_injection_mode.double_bit_error) : '0;
            end
        end
    `endif
   //=========================================================================-
   // SRAM instances
   //=========================================================================-


    caliptra_sram
    #(
        .DATA_WIDTH(MCU_MBOX0_DATA_AND_ECC_W),
        .DEPTH     (MCU_MBOX0_DEPTH         )
    )
    mcu_mbox0_ram
    (
        .clk_i(cptra_ss_rdc_clk_cg_o),

        .cs_i(cptra_ss_mcu_mbox0_sram_req_if.req.cs),
        .we_i(cptra_ss_mcu_mbox0_sram_req_if.req.we),
        .addr_i(cptra_ss_mcu_mbox0_sram_req_if.req.addr),
        .wdata_i(cptra_ss_mcu_mbox0_sram_req_if.req.wdata ^ mbox0_sram_wdata_bitflip),

        .rdata_o(cptra_ss_mcu_mbox0_sram_req_if.resp.rdata)
    );
    
    caliptra_sram
    #(
        .DATA_WIDTH(MCU_MBOX1_DATA_AND_ECC_W),
        .DEPTH     (MCU_MBOX1_DEPTH         )
    )
    mcu_mbox1_ram
    (
        .clk_i(cptra_ss_rdc_clk_cg_o),

        .cs_i(cptra_ss_mcu_mbox1_sram_req_if.req.cs),
        .we_i(cptra_ss_mcu_mbox1_sram_req_if.req.we),
        .addr_i(cptra_ss_mcu_mbox1_sram_req_if.req.addr),
        .wdata_i(cptra_ss_mcu_mbox1_sram_req_if.req.wdata ^ mbox1_sram_wdata_bitflip),

        .rdata_o(cptra_ss_mcu_mbox1_sram_req_if.resp.rdata)
    );


    rom #(
        .DEPTH     (CPTRA_SS_ROM_DEPTH), // 256KiB
        .DATA_WIDTH(CPTRA_SS_ROM_DATA_W)
    ) imem (
        .clk_i   (clk),
        .cs_i    (mcu_rom_mem_export_if.req.cs),
        .we_i    (mcu_rom_mem_export_if.req.we),
        .addr_i  (mcu_rom_mem_export_if.req.addr),
        .wdata_i (mcu_rom_mem_export_if.req.wdata),
        .rdata_o (mcu_rom_mem_export_if.resp.rdata)
    );

    caliptra_ss_sram #(
        .DEPTH     (MCU_SRAM_DEPTH),
        .DATA_WIDTH(MCU_SRAM_DATA_TOTAL_WIDTH),
        .ADDR_WIDTH(MCU_SRAM_ADDR_WIDTH)
   ) lmem (
       .clk_i   (cptra_ss_rdc_clk_cg_o),
       .cs_i    (cptra_ss_mci_mcu_sram_req_if.req.cs),
       .we_i    (cptra_ss_mci_mcu_sram_req_if.req.we),
       .addr_i  (cptra_ss_mci_mcu_sram_req_if.req.addr),
       .wdata_i (cptra_ss_mci_mcu_sram_req_if.req.wdata ^ mcu_sram_wdata_bitflip),
       .rdata_o (cptra_ss_mci_mcu_sram_req_if.resp.rdata)
   );

    // -- LMEM PRELOAD
    caliptra_sram #(
         .DEPTH     (MCU_SRAM_DEPTH        ), 
         .DATA_WIDTH(MCU_SRAM_DATA_WIDTH   ), 
         .ADDR_WIDTH(MCU_SRAM_ADDR_WIDTH   )

    ) lmem_dummy_preloader (
        .clk_i   (clk),

        .cs_i    (        ),
        .we_i    (        ),
        .addr_i  (        ),
        .wdata_i (        ),
        .rdata_o (        )
    );


task preload_mcu_sram;
    bit[MCU_SRAM_ECC_WIDTH-1:0] ecc;
    bit[MCU_SRAM_DATA_WIDTH-1:0] data;
    bit[31:0] addr;

    `ifndef VERILATOR
    lmem.ram = '{default: '0};
    `endif
    $display("MCU SRAM pre-load from %h to %h", 0, MCU_SRAM_DEPTH-1);

    for(addr= 0; addr < MCU_SRAM_DEPTH; addr++) begin
        data = {lmem_dummy_preloader.ram[addr][3],lmem_dummy_preloader.ram[addr][2],lmem_dummy_preloader.ram[addr][1],lmem_dummy_preloader.ram[addr][0]};
        ecc = |data  ? riscv_ecc32(data) : 0; 
        lmem.ram[addr] = {ecc,data};
    end

endtask


caliptra_ss_veer_sram_export veer_sram_export_inst (
    .cptra_ss_mcu0_el2_mem_export
);


`ifdef VERILATOR
`define MCU_DRAM(bk) veer_sram_export_inst.css_mcu0_dccm_enable.dccm_loop[bk].ram.ram_core
`else
`define MCU_DRAM(bk) veer_sram_export_inst.css_mcu0_dccm_enable.dccm_loop[bk].dccm.dccm_bank.ram_core
`endif







function[6:0] riscv_ecc32(input[31:0] data);
    reg[6:0] synd;
    synd[0] = ^(data & 32'h56aa_ad5b);
    synd[1] = ^(data & 32'h9b33_366d);
    synd[2] = ^(data & 32'he3c3_c78e);
    synd[3] = ^(data & 32'h03fc_07f0);
    synd[4] = ^(data & 32'h03ff_f800);
    synd[5] = ^(data & 32'hfc00_0000);
    synd[6] = ^{data, synd[5:0]};
    return synd;
endfunction

function int get_dccm_bank(input[31:0] addr,  output int bank_idx);
    `ifdef css_mcu0_RV_DCCM_NUM_BANKS_2
        bank_idx = int'(addr[`css_mcu0_RV_DCCM_BITS-1:3]);
        return int'( addr[2]);
    `elsif css_mcu0_RV_DCCM_NUM_BANKS_4
        bank_idx = int'(addr[`css_mcu0_RV_DCCM_BITS-1:4]);
        return int'(addr[3:2]);
    `elsif css_mcu0_RV_DCCM_NUM_BANKS_8
        bank_idx = int'(addr[`css_mcu0_RV_DCCM_BITS-1:5]);
        return int'( addr[4:2]);
    `endif
endfunction

task dump_signature ();
        integer fp, i;

        $display("Dumping memory signature (0x%08X - 0x%08X)...",
            mem_signature_begin,
            mem_signature_end
        );

        fp = $fopen("veer.signature", "w");
        for (i=mem_signature_begin; i<mem_signature_end; i=i+4) begin

            // From DCCM
    `ifdef css_mcu0_RV_DCCM_ENABLE
            if (i >= `css_mcu0_RV_DCCM_SADR && i < `css_mcu0_RV_DCCM_EADR) begin
                bit[38:0] data;
                int bank, indx;
                bank = get_dccm_bank(i, indx);

                case (bank)
                0: data = `MCU_DRAM(0)[indx];
                1: data = `MCU_DRAM(1)[indx];
                `ifdef css_mcu0_RV_DCCM_NUM_BANKS_4
                2: data = `MCU_DRAM(2)[indx];
                3: data = `MCU_DRAM(3)[indx];
                `endif
                `ifdef css_mcu0_RV_DCCM_NUM_BANKS_8
                2: data = `MCU_DRAM(2)[indx];
                3: data = `MCU_DRAM(3)[indx];
                4: data = `MCU_DRAM(4)[indx];
                5: data = `MCU_DRAM(5)[indx];
                6: data = `MCU_DRAM(6)[indx];
                7: data = `MCU_DRAM(7)[indx];
                `endif
                endcase

                $fwrite(fp, "%08X\n", data[31:0]);
            end else
    `endif
            // From RAM
            begin
                $fwrite(fp, "%02X%02X%02X%02X\n",
                    lmem.ram[i+3],
                    lmem.ram[i+2],
                    lmem.ram[i+1],
                    lmem.ram[i+0]
                );
            end
        end

        $fclose(fp);
endtask



// -- DCCM PRELOAD
caliptra_sram #(
     .DEPTH     (16384        ), // 128KiB
     .DATA_WIDTH(64           ),
     .ADDR_WIDTH($clog2(16384))

) css_mcu0_dummy_dccm_preloader (
    .clk_i   (clk),

    .cs_i    (        ),
    .we_i    (        ),
    .addr_i  (        ),
    .wdata_i (        ),
    .rdata_o (        )
);

task static init_css_mcu0_dccm;
    `ifdef css_mcu0_RV_DCCM_ENABLE
        `MCU_DRAM(0) = '{default:39'h0};
        `MCU_DRAM(1) = '{default:39'h0};
    `ifdef css_mcu0_RV_DCCM_NUM_BANKS_4
        `MCU_DRAM(2) = '{default:39'h0};
        `MCU_DRAM(3) = '{default:39'h0};
    `endif
    `ifdef css_mcu0_RV_DCCM_NUM_BANKS_8
        `MCU_DRAM(4) = '{default:39'h0};
        `MCU_DRAM(5) = '{default:39'h0};
        `MCU_DRAM(6) = '{default:39'h0};
        `MCU_DRAM(7) = '{default:39'h0};
    `endif
    `endif
endtask

task slam_dccm_ram(input [31:0] addr, input[38:0] data);
    int bank, indx;
    bank = get_dccm_bank(addr, indx);
    `ifdef css_mcu0_RV_DCCM_ENABLE
    case(bank)
    0: `MCU_DRAM(0)[indx] = data;
    1: `MCU_DRAM(1)[indx] = data;
    `ifdef css_mcu0_RV_DCCM_NUM_BANKS_4
    2: `MCU_DRAM(2)[indx] = data;
    3: `MCU_DRAM(3)[indx] = data;
    `endif
    `ifdef css_mcu0_RV_DCCM_NUM_BANKS_8
    2: `MCU_DRAM(2)[indx] = data;
    3: `MCU_DRAM(3)[indx] = data;
    4: `MCU_DRAM(4)[indx] = data;
    5: `MCU_DRAM(5)[indx] = data;
    6: `MCU_DRAM(6)[indx] = data;
    7: `MCU_DRAM(7)[indx] = data;
    `endif
    endcase
    `endif
    //$display("Writing bank %0d indx=%0d A=%h, D=%h",bank, indx, addr, data);
endtask

task static preload_css_mcu0_dccm;
    bit[31:0] data;
    bit[31:0] addr, saddr, eaddr;

    `ifndef VERILATOR
    init_css_mcu0_dccm();
    `endif
    saddr = `css_mcu0_RV_DCCM_SADR;
    if (saddr < `css_mcu0_RV_DCCM_SADR || saddr > `css_mcu0_RV_DCCM_EADR) return;
    `ifndef css_mcu0_RV_DCCM_ENABLE
        $display("********************************************************");
        $display("DCCM preload: there is no DCCM in VeeR, terminating !!!");
        $display("********************************************************");
        $finish;
    `endif
    eaddr = `css_mcu0_RV_DCCM_EADR;
    $display("CSS MCU0 DCCM pre-load from %h to %h", saddr, eaddr);

    for(addr=saddr; addr <= eaddr; addr+=4) begin
        // FIXME hardcoded address indices?
        data = {css_mcu0_dummy_dccm_preloader.ram [addr[16:3]] [{addr[2],2'h3}],
                css_mcu0_dummy_dccm_preloader.ram [addr[16:3]] [{addr[2],2'h2}],
                css_mcu0_dummy_dccm_preloader.ram [addr[16:3]] [{addr[2],2'h1}],
                css_mcu0_dummy_dccm_preloader.ram [addr[16:3]] [{addr[2],2'h0}]};
        slam_dccm_ram(addr, data == 0 ? 0 : {riscv_ecc32(data),data});
    end
    $display("CSS MCU0 DCCM pre-load completed");

endtask


`ifndef VERILATOR
    lc_ctrl_cov_bind i_lc_ctrl_cov_bind();
    mci_top_cov_bind i_mci_top_cov_bind();
    caliptra_ss_top_cov_bind i_caliptra_ss_top_cov_bind();
`endif


/* verilator lint_off CASEINCOMPLETE */
`include "mcu_dasm.svi"
/* verilator lint_on CASEINCOMPLETE */


endmodule
