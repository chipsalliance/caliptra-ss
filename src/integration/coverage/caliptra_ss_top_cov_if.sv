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

`ifndef VERILATOR

`include "soc_address_map_defines.svh"

interface caliptra_ss_top_cov_if   
    import soc_ifc_pkg::*;  
    (
    input logic cptra_ss_clk_i,
    //SoC AXI Interface
    axi_if.w_mgr cptra_ss_cptra_core_m_axi_if_w_mgr,
    axi_if.r_mgr cptra_ss_cptra_core_m_axi_if_r_mgr,
    input logic cptra_ss_rst_b_i,
    input logic cptra_ss_pwrgood_i
);

    logic cptra_ss_cptra_core_m_axi_if_ar_hshake;
    logic cptra_ss_cptra_core_m_axi_if_aw_hshake;
    logic wdt_timer1_en;
    logic wdt_timer2_en;
    logic nmi_int;

    always_comb cptra_ss_cptra_core_m_axi_if_ar_hshake = cptra_ss_cptra_core_m_axi_if.arvalid && cptra_ss_cptra_core_m_axi_if.arready;
    always_comb cptra_ss_cptra_core_m_axi_if_aw_hshake = cptra_ss_cptra_core_m_axi_if.awvalid && cptra_ss_cptra_core_m_axi_if.awready;

    always_comb wdt_timer1_en = caliptra_ss_top.mci_top_i.i_mci_wdt_top.timer1_en;
    always_comb wdt_timer2_en = caliptra_ss_top.mci_top_i.i_mci_wdt_top.timer2_en;
    always_comb nmi_int = caliptra_ss_top.mci_mcu_nmi_int;
    always_comb cptra_ss_cptra_core_m_axi_if_ar_hshake = cptra_ss_cptra_core_m_axi_if_r_mgr.arvalid && cptra_ss_cptra_core_m_axi_if_r_mgr.arready;
    always_comb cptra_ss_cptra_core_m_axi_if_aw_hshake = cptra_ss_cptra_core_m_axi_if_w_mgr.awvalid && cptra_ss_cptra_core_m_axi_if_w_mgr.awready;
    
    covergroup caliptra_ss_top_cov_grp @(posedge cptra_ss_clk_i);
        option.per_instance = 1;
        //-----------------------------------------
        //AXI Manager Coverpoints
        //-----------------------------------------
        axi_rd_txn: coverpoint cptra_ss_cptra_core_m_axi_if_ar_hshake {
            bins single_axi_rd_txn = (0 => 1 => 0);
            bins b2b_axi_rd_txn = (1 [*5]); //5 rd txns in a row
        }
        axi_rd_rsp: coverpoint cptra_ss_cptra_core_m_axi_if_r_mgr.rvalid && cptra_ss_cptra_core_m_axi_if_r_mgr.rready {
            bins axi_rd_hshake = {1'b1};
            bins single_axi_rd_rsp = (0 => 1 => 0);
        }
        axi_wr_txn: coverpoint cptra_ss_cptra_core_m_axi_if_aw_hshake {
            bins single_axi_wr_txn = (0 => 1 => 0);
            bins b2b_axi_wr_txn = (1 [*5]); //5 wr txns in a row
        }
        axi_wr_rsp: coverpoint cptra_ss_cptra_core_m_axi_if_w_mgr.bvalid && cptra_ss_cptra_core_m_axi_if_w_mgr.bready {
            bins axi_wr_hshake = {1'b1};
            bins single_axi_wr_rsp = (0 => 1 => 0);
        }
        axi_any_txn:coverpoint (cptra_ss_cptra_core_m_axi_if_ar_hshake) || (cptra_ss_cptra_core_m_axi_if_aw_hshake) {
            bins single_axi_txn = (0 => 1 => 0);
            bins b2b_axi_txn = (1 [*5]); //5 txns in a row
        }

        axi_rd_mci_regs: coverpoint cptra_ss_cptra_core_m_axi_if_ar_hshake && cptra_ss_cptra_core_m_axi_if_r_mgr.araddr inside {[`SOC_MCI_TOP_BASE_ADDR:`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_BASE_ADDR-4]} {
            bins axi_rd_req = {1'b1};
        }
        axi_wr_mci_regs: coverpoint cptra_ss_cptra_core_m_axi_if_aw_hshake && cptra_ss_cptra_core_m_axi_if_w_mgr.awaddr inside {[`SOC_MCI_TOP_BASE_ADDR:`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_BASE_ADDR-4]} {
            bins axi_wr_req = {1'b1};
        }
        axi_rd_mcu_sram: coverpoint cptra_ss_cptra_core_m_axi_if_ar_hshake && cptra_ss_cptra_core_m_axi_if_r_mgr.araddr inside {[`SOC_MCI_TOP_MCU_SRAM_BASE_ADDR:`SOC_MCI_TOP_MCU_SRAM_END_ADDR]} {
            bins axi_rd_req = {1'b1};
        }
        axi_wr_mcu_sram: coverpoint cptra_ss_cptra_core_m_axi_if_aw_hshake && cptra_ss_cptra_core_m_axi_if_w_mgr.awaddr inside {[`SOC_MCI_TOP_MCU_SRAM_BASE_ADDR:`SOC_MCI_TOP_MCU_SRAM_END_ADDR]} {
            bins axi_wr_req = {1'b1};
        }
        // FIXME replace these magic numbers with some macro once soc_address_map is updated
        axi_rd_fc_regs: coverpoint cptra_ss_cptra_core_m_axi_if_ar_hshake && cptra_ss_cptra_core_m_axi_if_r_mgr.araddr inside {[64'h7000_0000:64'h7000_03FF]} {
            bins axi_rd_req = {1'b1};
        }
        axi_wr_fc_regs: coverpoint cptra_ss_cptra_core_m_axi_if_aw_hshake && cptra_ss_cptra_core_m_axi_if_w_mgr.awaddr inside {[64'h7000_0000:64'h7000_03FF]} {
            bins axi_wr_req = {1'b1};
        }

        //-----------------------------------------
        //WDT coverpoints
        //-----------------------------------------
        wdt_t1: coverpoint wdt_timer1_en;
        wdt_t2: coverpoint wdt_timer2_en;
        wdt_t1Xt2: cross wdt_t1, wdt_t2;
        // wdt_t1t2Xwarmrst: cross wdt_t1Xt2, cptra_rst_b;
        // wdt_t1t2Xcoldrst: cross wdt_t1Xt2, cptra_pwrgood;
        nmi:    coverpoint nmi_int;
    endgroup
    caliptra_ss_top_cov_grp caliptra_ss_top_cov_grp1 = new();
//    logic clk_gating_en;
//    logic cpu_halt_status;
//
//    assign clk_gating_en = caliptra_top.cg.clk_gate_en;
//    assign cpu_halt_status = caliptra_top.cg.cpu_halt_status;
//    
//
//    covergroup caliptra_top_cov_grp @(posedge clk);
//        option.per_instance = 1;
//   
//
//        //-----------------------------------------
//        //CLK GATING coverpoints
//        //-----------------------------------------
//        axi_rd_txn:         coverpoint s_axi_r_if.arvalid && s_axi_r_if.arready {
//            bins single_axi_rd_txn = (0 => 1 => 0);
//            bins b2b_axi_rd_txn = (1 [*5]); //5 rd txns in a row
//        }
//        axi_rd_rsp:         coverpoint s_axi_r_if.rvalid && s_axi_r_if.rready {
//            bins axi_rd_hshake = {1'b1};
//            bins single_axi_rd_rsp = (0 => 1 => 0);
//        }
//        axi_wr_txn:         coverpoint s_axi_w_if.awvalid && s_axi_w_if.awready {
//            bins single_axi_wr_txn = (0 => 1 => 0);
//            bins b2b_axi_wr_txn = (1 [*5]); //5 wr txns in a row
//        }
//        axi_wr_rsp:         coverpoint s_axi_w_if.bvalid && s_axi_w_if.bready {
//            bins axi_wr_hshake = {1'b1};
//            bins single_axi_wr_rsp = (0 => 1 => 0);
//        }
//        axi_any_txn:        coverpoint (s_axi_r_if.arvalid && s_axi_r_if.arready) || (s_axi_w_if.awvalid && s_axi_w_if.awready) {
//            bins single_axi_txn = (0 => 1 => 0);
//            bins b2b_axi_txn = (1 [*5]); //5 txns in a row
//        }
//        cg_en:              coverpoint clk_gating_en;
//        core_asleep_value:  coverpoint cpu_halt_status;
//        core_asleep_trans:  coverpoint cpu_halt_status {
//            bins bin01 = (0 => 1);
//            bins bin10 = (1 => 0);
//        }
//        warm_rst:           coverpoint cptra_rst_b;
//
//        scan:               coverpoint scan_mode;
//        debug:              coverpoint security_state.debug_locked;
//        fatal_error:        coverpoint cptra_error_fatal;
//        generic:            coverpoint generic_input_wires;
//
//        enXcore_asleep:             cross cg_en, core_asleep_value {
//            ignore_bins b0 = enXcore_asleep with ((cg_en == 0) && (core_asleep_value == 1));
//        }
//        enXcore_asleepXwarm_rst:    cross enXcore_asleep, warm_rst;
//        enXcore_asleepXcold_rst:    cross enXcore_asleep, cptra_pwrgood;
//        // {
//        //     ignore_bins b0 = enXcore_asleepXwarm_rst with ((cg_en == 1) && (core_asleep_value == 1) && (warm_rst == 0));
//        // }
//        enXcore_asleepXwdt1:        cross enXcore_asleep, wdt_t1;
//        enXcore_asleepXwdt2:        cross enXcore_asleep, wdt_t2;
//
//        enXcore_asleepXscan:        cross enXcore_asleep, scan;
//        enXcore_asleepXdebug:       cross enXcore_asleep, debug;
//        enXcore_asleepXfatalerr:    cross enXcore_asleep, fatal_error;
//        enXcore_asleepXnmi:         cross enXcore_asleep, nmi;
//        enXcore_asleepXaxi:         cross enXcore_asleep, axi_any_txn;
//        enXcore_asleepXgeneric:     cross enXcore_asleep, generic;
//    endgroup
//
//    covergroup generic_input_wires_cg(input logic generic_bit) @(posedge clk);
//        option.per_instance = 1;
//        value:      coverpoint generic_bit;
//        transition: coverpoint generic_bit {
//            bins bin01 = (0 => 1);
//            bins bin10 = (1 => 0);
//        }
//    endgroup
//
//    // CLK_GATING_cov_grp CLK_GATING_cov_grp1 = new();
//    // WDT_cov_grp WDT_cov_grp1 = new();
//    caliptra_top_cov_grp caliptra_top_cov_grp1 = new();
//    
//    generic_input_wires_cg giw_cg[64];
//    //foreach(giw_cg[i]) giw_cg[i] = new(generic_input_wires[i]);
//    initial begin
//        for(int i = 0; i < 64; i++) begin
//            giw_cg[i] = new(generic_input_wires[i]);
//        end
//    end

endinterface

`endif
