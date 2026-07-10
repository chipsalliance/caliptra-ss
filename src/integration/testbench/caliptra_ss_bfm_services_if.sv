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


interface caliptra_ss_bfm_services_if (
);

    `include "caliptra_ss_includes.svh"
    import css_mcu0_el2_pkg::*;
    `include "css_mcu0_el2_param.vh"
    ;

    // Define signals
    logic deassert_hard_rst_flag;
    logic assert_hard_rst_flag;
    logic deassert_rst_flag;
    logic assert_rst_flag;
    logic deassert_hard_rst_flag_done;
    logic assert_hard_rst_flag_done;
    logic deassert_rst_flag_done;
    logic assert_rst_flag_done;

    logic [pt.PIC_TOTAL_INT:`VEER_INTR_EXT_LSB] toggle_cptra_ss_mcu_ext_int;
    
    logic end_test_success;

    // Define modports
    modport bfm (
        output end_test_success,
        input  deassert_hard_rst_flag,
        input  assert_hard_rst_flag,
        input  deassert_rst_flag,
        input  assert_rst_flag,
        output deassert_hard_rst_flag_done,
        output assert_hard_rst_flag_done,
        output deassert_rst_flag_done,
        output assert_rst_flag_done,
        input  toggle_cptra_ss_mcu_ext_int
    );

    modport tb_services (
        input  end_test_success,
        output deassert_hard_rst_flag,
        output assert_hard_rst_flag,
        output deassert_rst_flag,
        output assert_rst_flag,
        input  deassert_hard_rst_flag_done,
        input  assert_hard_rst_flag_done,
        input  deassert_rst_flag_done,
        input  assert_rst_flag_done,
        output toggle_cptra_ss_mcu_ext_int
    );
endinterface

