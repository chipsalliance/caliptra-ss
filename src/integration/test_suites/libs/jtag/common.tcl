# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License")
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

set dmstatus_addr 0x11
set dmcontrol_addr 0x10

proc compare {x y} {
    puts "'$x' vs. '$y'"

    if {[llength $y] != [llength $y]} {
        puts "length mismatch!"
        return -1
    }

    for {set i 0} {$i < [llength $x]} {incr i} {
        if {[lindex $x $i] != [lindex $y $i]} {
            puts "item $i mismatch!"
            return -1
        }
    }

    return 0
}
proc halt_core {} {
    puts "Halting the core..."
    riscv dmi_write $dmcontrol_addr 0x80000001
    puts "Read Debug Module Status Register..."
    set val [riscv dmi_read $dmstatus_addr]
    puts "dmstatus: $val"
    while {($val & 0x00000300) == 0} {
        puts "The hart is not halted yet!"
        set val [riscv dmi_read $dmstatus_addr]
    }
    puts "The hart is halted!"
}

set STDOUT 0x300300cc
set MCU_STDOUT 0x21000414

set mbox_clk_gate_en 0xf2
set mbox_lock_debug 0xf9
set mbox_unlock_debug 0xfa

set mbox_lock_mem_addr 0x30020000
set mbox_user_mem_addr 0x30020004
set mbox_cmd_mem_addr 0x30020008
set mbox_dlen_mem_addr 0x3002000C
set mbox_datain_mem_addr 0x30020010
set mbox_dataout_mem_addr 0x30020014
set mbox_execute_mem_addr 0x30020018
set mbox_status_mem_addr 0x3002001C
set mbox_unlock_mem_addr 0x30020020

set mbox_dlen_dmi_addr 0x50
set mbox_dout_dmi_addr 0x51
set mbox_status_dmi_addr 0x52

#dmi register addresses
set mbox_dlen_dmi_addr 0x50
set mbox_dout_dmi_addr 0x51
set mbox_status_dmi_addr 0x52

#Caliptra Uncore DMI Register encodings
#Mailbox registers
set dmi_reg_mbox_dout 0x51
set dmi_reg_mbox_dlen 0x50
set dmi_reg_mbox_din 0x62
set dmi_reg_mbox_status 0x52
set dmi_reg_mbox_lock 0x75
set dmi_reg_mbox_cmd 0x76
set dmi_reg_mbox_execute 0x77

#Read only registers
set dmi_reg_boot_status 0x53
set dmi_reg_cptra_hw_errror_enc 0x54
set dmi_reg_cptra_fw_error_enc 0x55
set dmi_reg_ss_uds_seed_base_addr_l 0x56
set dmi_reg_ss_uds_seed_base_addr_h 0x57
set dmi_reg_hw_fatal_error 0x58
set dmi_reg_fw_fatal_error 0x59
set dmi_reg_hw_non_fatal_error 0x5a
set dmi_reg_fw_non_fatal_error 0x5b

set mem_reg_boot_status 0x30030038
set mem_reg_cptra_hw_errror_enc 0x30030010
set mem_reg_cptra_fw_error_enc 0x30030014
set mem_reg_ss_uds_seed_base_addr_l 0x30030520
set mem_reg_ss_uds_seed_base_addr_h 0x30030524
set mem_reg_hw_fatal_error 0x30030000
set mem_reg_fw_fatal_error 0x30030008
set mem_reg_hw_non_fatal_error 0x30030004
set mem_reg_fw_non_fatal_error 0x3003000c

#RW registers
set dmi_reg_cptra_dbg_manuf_service_reg 0x60
set dmi_reg_bootfsm_go 0x61
set dmi_reg_ss_debug_intent 0x63
set dmi_reg_ss_caliptra_base_addr_l 0x64
set dmi_reg_ss_caliptra_base_addr_h 0x65
set dmi_reg_ss_mci_base_addr_l 0x66
set dmi_reg_ss_mci_base_addr_h 0x67
set dmi_reg_ss_recovery_ifc_base_addr_l 0x68
set dmi_reg_ss_recovery_ifc_base_addr_h 0x69
set dmi_reg_ss_otp_fc_base_addr_l 0x6a
set dmi_reg_ss_otp_fc_base_addr_h 0x6b
set dmi_reg_ss_strap_generic_0 0x6c
set dmi_reg_ss_strap_generic_1 0x6d
set dmi_reg_ss_strap_generic_2 0x6e
set dmi_reg_ss_strap_generic_3 0x6f
set dmi_reg_ss_dbg_manuf_service_reg_req 0x70
set dmi_reg_ss_dbg_manuf_service_reg_rsp 0x71
set dmi_reg_ss_dbg_unlock_level0 0x72
set dmi_reg_ss_dbg_unlock_level1 0x73
set dmi_reg_ss_strap_caliptra_dma_axi_user 0x74

#MCI Uncore DMI Register encodings
# MCI MBOX DMI ALL RO
set MCI_DMI_REG_MBOX0_DLEN    0x50
set MCI_DMI_REG_MBOX0_DOUT    0x51
set MCI_DMI_REG_MBOX0_STATUS  0x52
set MCI_DMI_REG_MBOX0_DIN     0x53
set MCI_DMI_REG_MBOX1_DLEN    0x54
set MCI_DMI_REG_MBOX1_DOUT    0x55
set MCI_DMI_REG_MBOX1_STATUS  0x56
set MCI_DMI_REG_MBOX1_DIN     0x57
    

#MCU SRAM DMI (ALL RW)
set MCI_DMI_MCU_SRAM_ADDR     0x58
set MCI_DMI_MCU_SRAM_DATA     0x59
    
#MCU TRACE DMI 
set MCI_DMI_MCU_TRACE_STATUS 0x5A
set MCI_DMI_MCU_TRACE_CONFIG 0x5B
set MCI_DMI_MCU_TRACE_WR_PTR 0x5C
set MCI_DMI_MCU_TRACE_RD_PTR 0x5D
set MCI_DMI_MCU_TRACE_DATA   0x5E
    
#MCI REG DMI RO
set MCI_DMI_HW_FLOW_STATUS            0x5F
set MCI_DMI_RESET_REASON              0x60
set MCI_DMI_RESET_STATUS              0x61
set MCI_DMI_FW_FLOW_STATUS            0x62
set MCI_DMI_HW_ERROR_FATAL            0x63
set MCI_DMI_AGG_ERROR_FATAL           0x64
set MCI_DMI_HW_ERROR_NON_FATAL        0x65
set MCI_DMI_AGG_ERROR_NON_FATAL       0x66
set MCI_DMI_FW_ERROR_FATAL            0x67
set MCI_DMI_FW_ERROR_NON_FATAL        0x68
set MCI_DMI_HW_ERROR_ENC              0x69
set MCI_DMI_FW_ERROR_ENC              0x6A
set MCI_DMI_FW_EXTENDED_ERROR_INFO_0  0x6B
set MCI_DMI_FW_EXTENDED_ERROR_INFO_1  0x6C
set MCI_DMI_FW_EXTENDED_ERROR_INFO_2  0x6D
set MCI_DMI_FW_EXTENDED_ERROR_INFO_3  0x6E
set MCI_DMI_FW_EXTENDED_ERROR_INFO_4  0x6F
set MCI_DMI_FW_EXTENDED_ERROR_INFO_5  0x70
set MCI_DMI_FW_EXTENDED_ERROR_INFO_6  0x71
set MCI_DMI_FW_EXTENDED_ERROR_INFO_7  0x72

#MCI REG MEM RO
set MCI_MEM_HW_FLOW_STATUS            0x21000034
set MCI_MEM_RESET_REASON              0x21000038
set MCI_MEM_RESET_STATUS              0x2100003c
set MCI_MEM_FW_FLOW_STATUS            0x21000030
set MCI_MEM_HW_ERROR_FATAL            0x21000050
set MCI_MEM_AGG_ERROR_FATAL           0x21000054
set MCI_MEM_HW_ERROR_NON_FATAL        0x21000058
set MCI_MEM_AGG_ERROR_NON_FATAL       0x2100005c
set MCI_MEM_FW_ERROR_FATAL            0x21000060
set MCI_MEM_FW_ERROR_NON_FATAL        0x21000064
set MCI_MEM_HW_ERROR_ENC              0x21000068
set MCI_MEM_FW_ERROR_ENC              0x2100006c
set MCI_MEM_FW_EXTENDED_ERROR_INFO_0  0x21000070
set MCI_MEM_FW_EXTENDED_ERROR_INFO_1  0x21000074
set MCI_MEM_FW_EXTENDED_ERROR_INFO_2  0x21000078
set MCI_MEM_FW_EXTENDED_ERROR_INFO_3  0x2100007c
set MCI_MEM_FW_EXTENDED_ERROR_INFO_4  0x21000080
set MCI_MEM_FW_EXTENDED_ERROR_INFO_5  0x21000084
set MCI_MEM_FW_EXTENDED_ERROR_INFO_6  0x21000088
set MCI_MEM_FW_EXTENDED_ERROR_INFO_7  0x2100008c
set MCI_MEM_MCU_RESET_VECTOR          0x21000114
#MCI REG DMI RW
set MCI_DMI_RESET_REQUEST             0x73
set MCI_DMI_MCI_BOOTFSM_GO            0x74
set MCI_DMI_CPTRA_BOOT_GO             0x75
set MCI_DMI_FW_SRAM_EXEC_REGION_SIZE  0x76
set MCI_DMI_MCU_RESET_VECTOR          0x77
set MCI_DMI_SS_DEBUG_INTENT           0x78
set MCI_DMI_SS_CONFIG_DONE            0x79
set MCI_DMI_SS_CONFIG_DONE_STICKY     0x7A
set MCI_DMI_MCU_NMI_VECTOR            0x7B
set MCI_DMI_MCI_HW_OVERRIDE           0x7C