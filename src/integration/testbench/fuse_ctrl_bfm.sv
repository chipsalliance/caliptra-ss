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

module fuse_ctrl_bfm
    import lc_ctrl_pkg::*;
    //import caliptra_top_tb_pkg::*;
    //import global_fuse_ctrl_init_done_event_pkg::*;
    (
        input logic         core_clk,
        input logic         cptra_pwrgood,
        output logic        fc_partition_init,
        output lc_tx_t      lc_dft_en_i,
        output lc_tx_t      lc_escalate_en_i,
        output lc_tx_t      lc_check_byp_en_i,
        input logic         otp_lc_data_o_valid,
        output logic        fuse_ctrl_rdy
    );

    initial begin
        fuse_ctrl_rst();
        fuse_ctrl_rdy = 0;
        wait(cptra_pwrgood == 1);
        $display("Fuse Controller (fuse_ctrl_init_flow): Forcing fc_partition_init = 1.");
        force fc_partition_init = 1'b1;
        wait(otp_lc_data_o_valid == 1);
        //->caliptra_top_tb_pkg::fuse_ctrl_init_done; //Signal that fuse controler initialization is done
        fuse_ctrl_rdy = 1;
        $display("Fuse Controller (fuse_ctrl_init_flow): All partitions initialized.");
        $display("Fuse Controller (fuse_ctrl_init_flow): Releasing fc_partition_init = 1. ");
        release fc_partition_init;
    end

    task fuse_ctrl_rst();
        lc_dft_en_i         = lc_ctrl_pkg::Off;
        lc_escalate_en_i    = lc_ctrl_pkg::Off;
        lc_check_byp_en_i   = lc_ctrl_pkg::Off;
        fc_partition_init   = 0;
    endtask
endmodule

