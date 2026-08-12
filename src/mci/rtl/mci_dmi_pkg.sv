
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

package mci_dmi_pkg;

    // UNCORE BASE ADDRESS: 0x50
    // UNCORE MAX ADDRESS: 0x7F

    // MCI MBOX DMI ALL RO
    parameter MCI_DMI_REG_MBOX0_DLEN    = 7'h50;
    parameter MCI_DMI_REG_MBOX0_DOUT    = 7'h51;
    parameter MCI_DMI_REG_MBOX0_STATUS  = 7'h52;
    parameter MCI_DMI_REG_MBOX0_DIN     = 7'h53;
    parameter MCI_DMI_REG_MBOX1_DLEN    = 7'h54;
    parameter MCI_DMI_REG_MBOX1_DOUT    = 7'h55;
    parameter MCI_DMI_REG_MBOX1_STATUS  = 7'h56;
    parameter MCI_DMI_REG_MBOX1_DIN     = 7'h57;
    

    // MCU SRAM DMI (ALL RW)
    parameter MCI_DMI_MCU_SRAM_ADDR     = 7'h58;
    parameter MCI_DMI_MCU_SRAM_DATA     = 7'h59;
    
    // MCU TRACE DMI 
    parameter MCI_DMI_MCU_TRACE_STATUS = 7'h5A; // RO
    parameter MCI_DMI_MCU_TRACE_CONFIG = 7'h5B; // RO
    parameter MCI_DMI_MCU_TRACE_WR_PTR = 7'h5C; // RO
    parameter MCI_DMI_MCU_TRACE_RD_PTR = 7'h5D; // RO
    parameter MCI_DMI_MCU_TRACE_DATA   = 7'h5E; // RO
    
    // MCI REG DMI RO
    parameter MCI_DMI_HW_FLOW_STATUS            = 7'h5F;
    parameter MCI_DMI_RESET_REASON              = 7'h60;
    parameter MCI_DMI_RESET_STATUS              = 7'h61;
    parameter MCI_DMI_FW_FLOW_STATUS            = 7'h62;
    parameter MCI_DMI_HW_ERROR_FATAL            = 7'h63;
    parameter MCI_DMI_AGG_ERROR_FATAL           = 7'h64;
    parameter MCI_DMI_HW_ERROR_NON_FATAL        = 7'h65;
    parameter MCI_DMI_AGG_ERROR_NON_FATAL       = 7'h66;
    parameter MCI_DMI_FW_ERROR_FATAL            = 7'h67;
    parameter MCI_DMI_FW_ERROR_NON_FATAL        = 7'h68;
    parameter MCI_DMI_HW_ERROR_ENC              = 7'h69;
    parameter MCI_DMI_FW_ERROR_ENC              = 7'h6A;
    parameter MCI_DMI_FW_EXTENDED_ERROR_INFO_0  = 7'h6B;
    parameter MCI_DMI_FW_EXTENDED_ERROR_INFO_1  = 7'h6C;
    parameter MCI_DMI_FW_EXTENDED_ERROR_INFO_2  = 7'h6D;
    parameter MCI_DMI_FW_EXTENDED_ERROR_INFO_3  = 7'h6E;
    parameter MCI_DMI_FW_EXTENDED_ERROR_INFO_4  = 7'h6F;
    parameter MCI_DMI_FW_EXTENDED_ERROR_INFO_5  = 7'h70;
    parameter MCI_DMI_FW_EXTENDED_ERROR_INFO_6  = 7'h71;
    parameter MCI_DMI_FW_EXTENDED_ERROR_INFO_7  = 7'h72;

    // MCI REG DMI RW
    parameter MCI_DMI_RESET_REQUEST             = 7'h73;
    parameter MCI_DMI_MCI_BOOTFSM_GO            = 7'h74;
    parameter MCI_DMI_CPTRA_BOOT_GO             = 7'h75;
    parameter MCI_DMI_FW_SRAM_EXEC_REGION_SIZE  = 7'h76;
    parameter MCI_DMI_MCU_RESET_VECTOR                  = 7'h77;
    // SS_DEBUG_INTENT is READ-ONLY over DMI/TAP: the TAP write override was removed,
    // so this register reflects only the physical debug-intent strap captured by MCI.
    parameter MCI_DMI_SS_DEBUG_INTENT                   = 7'h78; // RO
    parameter MCI_DMI_SS_CONFIG_DONE                    = 7'h79;
    parameter MCI_DMI_SS_CONFIG_DONE_STICKY             = 7'h7A;
    parameter MCI_DMI_MCU_NMI_VECTOR                    = 7'h7B;
    parameter MCI_DMI_MCI_HW_OVERRIDE                   = 7'h7C; 

    typedef struct packed{
        logic [30:0] reserved;
        logic mcu_sram_fw_exec_region_lock;
    } MCI_DMI_MCI_HW_OVERRIDE_REG_t;

    // Aggregate the 32 individually-named sticky error bits of an
    // AGG_ERROR_{FATAL,NON_FATAL} register into a single 32-bit word for the
    // DMI/TAP readback, ordered MSB=index 31 .. LSB=index 0. These replace the
    // former `SS_DMI_AGG_ERR_CONCAT text-substitution macro (a `define is not
    // appropriate inside a package): the register struct fields are discretely
    // named (agg_error_fatal0 .. agg_error_fatal31) rather than an array, so
    // each field is referenced explicitly.
    function automatic logic [31:0] mci_dmi_agg_error_fatal_concat(
        input mci_reg_pkg::mci_reg__AGG_ERROR_FATAL__out_t agg
    );
        return {agg.agg_error_fatal31.value, agg.agg_error_fatal30.value, agg.agg_error_fatal29.value, agg.agg_error_fatal28.value,
                agg.agg_error_fatal27.value, agg.agg_error_fatal26.value, agg.agg_error_fatal25.value, agg.agg_error_fatal24.value,
                agg.agg_error_fatal23.value, agg.agg_error_fatal22.value, agg.agg_error_fatal21.value, agg.agg_error_fatal20.value,
                agg.agg_error_fatal19.value, agg.agg_error_fatal18.value, agg.agg_error_fatal17.value, agg.agg_error_fatal16.value,
                agg.agg_error_fatal15.value, agg.agg_error_fatal14.value, agg.agg_error_fatal13.value, agg.agg_error_fatal12.value,
                agg.agg_error_fatal11.value, agg.agg_error_fatal10.value, agg.agg_error_fatal9.value,  agg.agg_error_fatal8.value,
                agg.agg_error_fatal7.value,  agg.agg_error_fatal6.value,  agg.agg_error_fatal5.value,  agg.agg_error_fatal4.value,
                agg.agg_error_fatal3.value,  agg.agg_error_fatal2.value,  agg.agg_error_fatal1.value,  agg.agg_error_fatal0.value};
    endfunction

    function automatic logic [31:0] mci_dmi_agg_error_non_fatal_concat(
        input mci_reg_pkg::mci_reg__AGG_ERROR_NON_FATAL__out_t agg
    );
        return {agg.agg_error_non_fatal31.value, agg.agg_error_non_fatal30.value, agg.agg_error_non_fatal29.value, agg.agg_error_non_fatal28.value,
                agg.agg_error_non_fatal27.value, agg.agg_error_non_fatal26.value, agg.agg_error_non_fatal25.value, agg.agg_error_non_fatal24.value,
                agg.agg_error_non_fatal23.value, agg.agg_error_non_fatal22.value, agg.agg_error_non_fatal21.value, agg.agg_error_non_fatal20.value,
                agg.agg_error_non_fatal19.value, agg.agg_error_non_fatal18.value, agg.agg_error_non_fatal17.value, agg.agg_error_non_fatal16.value,
                agg.agg_error_non_fatal15.value, agg.agg_error_non_fatal14.value, agg.agg_error_non_fatal13.value, agg.agg_error_non_fatal12.value,
                agg.agg_error_non_fatal11.value, agg.agg_error_non_fatal10.value, agg.agg_error_non_fatal9.value,  agg.agg_error_non_fatal8.value,
                agg.agg_error_non_fatal7.value,  agg.agg_error_non_fatal6.value,  agg.agg_error_non_fatal5.value,  agg.agg_error_non_fatal4.value,
                agg.agg_error_non_fatal3.value,  agg.agg_error_non_fatal2.value,  agg.agg_error_non_fatal1.value,  agg.agg_error_non_fatal0.value};
    endfunction

endpackage
