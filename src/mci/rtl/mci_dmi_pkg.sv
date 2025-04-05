
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

`ifndef MCI_DMI_PKG
    `define MCI_DMI_PKG

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
    parameter MCI_DMI_MCU_RESET_VECTOR          = 7'h77;
    parameter MCI_DMI_SS_DEBUG_INTENT           = 7'h78;
    parameter MCI_DMI_SS_CONFIG_DONE            = 7'h79;
    parameter MCI_DMI_SS_CONFIG_DONE_STICKY     = 7'h7A;
    parameter MCI_DMI_MCU_NMI_VECTOR            = 7'h7B;

    `define SS_DMI_AGG_ERR_CONCAT(_sig_name) \
    {``_sig_name``31.value,``_sig_name``30.value,``_sig_name``29.value,``_sig_name``28.value,\
     ``_sig_name``27.value,``_sig_name``26.value,``_sig_name``25.value,``_sig_name``24.value,\
     ``_sig_name``23.value,``_sig_name``22.value,``_sig_name``21.value,``_sig_name``20.value,\
     ``_sig_name``19.value,``_sig_name``18.value,``_sig_name``17.value,``_sig_name``16.value,\
     ``_sig_name``15.value,``_sig_name``14.value,``_sig_name``13.value,``_sig_name``12.value,\
     ``_sig_name``11.value,``_sig_name``10.value,``_sig_name``9.value, ``_sig_name``8.value,\
     ``_sig_name``7.value, ``_sig_name``6.value, ``_sig_name``5.value, ``_sig_name``4.value,\
     ``_sig_name``3.value, ``_sig_name``2.value, ``_sig_name``1.value, ``_sig_name``0.value}

endpackage
`endif
