# Caliptra SS Integration Specification

## Calpitra SS top level diagram - @Nilesh

### Overview

### Links to individual IPs

### Top level Address map

| Slave | Connected to  | Start Address | End Address |
|---|---|---|---|
| 0 | imem | 64'h1000_0000 | 64'h1000_FFFF |
| 1 | I3c | 64'h2000_4000 | 64'h2000_4FFF |
| 2 | n/a | 64'h8000_0000 | 64'h80FF_FFFF |
| 3 | SoC IFC (tb) | 64'h3000_0000,
  64'h0003_0000 | 64'h3FFF_FFFF,
  64'h0003_FFFF |
| 4 | MCI | 64'h2100_0000 | 64'h2200_0000 |
| 5 | Fuse Ctrl | 64'h7000_0000 | 64'h7000_01FF |
| 6 | Fuse Ctrl Core | 64'h7000_0200 | 64'h7000_03FF |
| 7 | Life Cycle Ctrl | 64'h7000_0400 | 64'h7000_05FF |

### Same as MCU

## Top level / remaining functional flows & signals. - @Nilesh

### Overview

### Parameters & Defines

### Interface


| Facing | Type | width | Name | Description |
|---|---|---|---|---|
| External | input | 1 | cptra_ss_clk_i | Caliptra subsystem clock input |
| External | input | 1 | cptra_ss_pwrgood_i | Power good signal input |
| External | input | 1 | cptra_ss_rst_b_i | Reset signal input, active low |
| External | interface | 1 | cptra_ss_cptra_core_s_axi_if | Caliptra core AXI sub-interface |
| External | interface | 1 | cptra_ss_cptra_core_m_axi_if | Caliptra core AXI manager interface |
| External | interface | 1 | cptra_ss_mci_s_axi_if | Caliptra SS MCI AXI sub-interface |
| External | interface | 1 | cptra_ss_mcu_rom_s_axi_if | Caliptra SS MCU ROM AXI sub-interface |
| External | interface | 1 | mcu_rom_mem_export_if | MCU ROM memory export interface |
| External | interface | 1 | cptra_ss_mci_m_axi_if | Caliptra SS MCI AXI manager interface |
| External | interface | 1 | cptra_ss_mcu_lsu_m_axi_if | Caliptra SS MCU LSU AXI manager interface |
| External | interface | 1 | cptra_ss_mcu_ifu_m_axi_if | Caliptra SS MCU IFU AXI manager interface |
| External | interface | 1 | cptra_ss_i3c_s_axi_if | Caliptra SS I3C AXI sub-interface |
| External | input | 1 | cptra_ss_lc_axi_wr_req_i | LC controller AXI write request input |
| External | output | 1 | cptra_ss_lc_axi_wr_rsp_o | LC controller AXI write response output |
| External | input | 1 | cptra_ss_lc_axi_rd_req_i | LC controller AXI read request input |
| External | output | 1 | cptra_ss_lc_axi_rd_rsp_o | LC controller AXI read response output |
| External | input | 1 | cptra_ss_otp_core_axi_wr_req_i | OTP controller AXI write request input |
| External | output | 1 | cptra_ss_otp_core_axi_wr_rsp_o | OTP controller AXI write response output |
| External | input | 1 | cptra_ss_otp_core_axi_rd_req_i | OTP controller AXI read request input |
| External | output | 1 | cptra_ss_otp_core_axi_rd_rsp_o | OTP controller AXI read response output |
| External | input | 1 | cptra_ss_cptra_obf_key_i | Caliptra core obfuscation key input |
| External | input | 1 | cptra_ss_cptra_csr_hmac_key_i | Caliptra core CSR HMAC key input |
| External | input | 1 | cptra_ss_cptra_core_jtag_tck_i | JTAG clock input |
| External | input | 1 | cptra_ss_cptra_core_jtag_tms_i | JTAG TMS input |
| External | input | 1 | cptra_ss_cptra_core_jtag_tdi_i | JTAG TDI input |
| External | input | 1 | cptra_ss_cptra_core_jtag_trst_n_i | JTAG reset input, active low |
| External | output | 1 | cptra_ss_cptra_core_jtag_tdo_o | JTAG TDO output |
| External | output | 1 | cptra_ss_cptra_core_jtag_tdoEn_o | JTAG TDO enable output |
| External | output | 1 | cptra_ss_cptra_generic_fw_exec_ctrl_o | Generic firmware execution control output |
| External | input | 1 | cptra_ss_lc_ctrl_jtag_i | LC controller JTAG request input |
| External | output | 1 | cptra_ss_lc_ctrl_jtag_o | LC controller JTAG response output |
| External | interface | 1 | cptra_ss_cptra_core_el2_mem_export | Caliptra core EL2 memory export interface |
| External | output | 1 | cptra_ss_cptra_core_mbox_sram_cs_o | Mailbox SRAM chip select output |
| External | output | 1 | cptra_ss_cptra_core_mbox_sram_we_o | Mailbox SRAM write enable output |
| External | output | 1 | cptra_sscptra_core_mbox_sram_addr_o | Mailbox SRAM address output |
| External | output | 1 | cptra_ss_cptra_core_mbox_sram_wdata_o | Mailbox SRAM write data output |
| External | input | 1 | cptra_ss_cptra_core_mbox_sram_rdata_i | Mailbox SRAM read data input |
| External | output | 1 | cptra_ss_cptra_core_imem_cs_o | Instruction memory chip select output |
| External | output | 1 | cptra_ss_cptra_core_imem_addr_o | Instruction memory address output |
| External | input | 1 | cptra_ss_cptra_core_imem_rdata_i | Instruction memory read data input |
| External | input | 1 | cptra_ss_cptra_core_bootfsm_bp_i | Boot FSM breakpoint input |
| External | output | 1 | cptra_ss_cptra_core_etrng_req_o | External TRNG request output |
| External | input | 1 | cptra_ss_cptra_core_itrng_data_i | Internal TRNG data input |
| External | input | 1 | cptra_ss_cptra_core_itrng_valid_i | Internal TRNG valid input |
| External | interface | 1 | cptra_ss_mcu_rom_macro_req_if | MCU ROM macro request interface |
| External | input | 1 | cptra_ss_strap_mcu_lsu_axi_user_i | MCU LSU AXI user strap input |
| External | input | 1 | cptra_ss_strap_mcu_ifu_axi_user_i | MCU IFU AXI user strap input |
| External | input | 1 | cptra_ss_strap_clp_axi_user_i | CLP AXI user strap input |
| External | interface | 1 | cptra_ss_mci_mcu_sram_req_if | MCI MCU SRAM request interface |
| External | interface | 1 | cptra_ss_mci_mbox0_sram_req_if | MCI mailbox 0 SRAM request interface |
| External | interface | 1 | cptra_ss_mci_mbox1_sram_req_if | MCI mailbox 1 SRAM request interface |
| External | interface | 1 | cptra_ss_mcu0_el2_mem_export | MCU0 EL2 memory export interface |
| External | input | 1 | cptra_ss_mci_generic_input_wires_i | Generic input wires for MCI |
| External | input | 1 | cptra_ss_strap_mcu_reset_vector_i | MCU reset vector strap input |
| External | input | 1 | cptra_ss_mcu_no_rom_config_i | No ROM configuration input |
| External | input | 1 | cptra_ss_mci_boot_seq_brkpoint_i | MCI boot sequence breakpoint input |
| External | input | 1 | cptra_ss_lc_Allow_RMA_on_PPD_i | Allow RMA on PPD input |
| External | output | 1 | cptra_ss_mci_generic_output_wires_o | Generic output wires for MCI |
| External | output | 1 | cptra_ss_mci_error_fatal_o | MCI error fatal output |
| External | output | 1 | cptra_ss_mci_error_non_fatal_o | MCI error non-fatal output |
| External | input | 1 | cptra_ss_mcu_jtag_tck_i | MCU JTAG clock input |
| External | input | 1 | cptra_ss_mcu_jtag_tms_i | MCU JTAG TMS input |
| External | input | 1 | cptra_ss_mcu_jtag_tdi_i | MCU JTAG TDI input |
| External | input | 1 | cptra_ss_mcu_jtag_trst_n_i | MCU JTAG reset input, active low |
| External | output | 1 | cptra_ss_mcu_jtag_tdo_o | MCU JTAG TDO output |
| External | output | 1 | cptra_ss_mcu_jtag_tdoEn_o | MCU JTAG TDO enable output |
| External | input | 1 | cptra_ss_strap_caliptra_base_addr_i | Caliptra base address strap input |
| External | input | 1 | cptra_ss_strap_mci_base_addr_i | MCI base address strap input |
| External | input | 1 | cptra_ss_strap_recovery_ifc_base_addr_i | Recovery interface base address strap input |
| External | input | 1 | cptra_ss_strap_otp_fc_base_addr_i | OTP FC base address strap input |
| External | input | 1 | cptra_ss_strap_uds_seed_base_addr_i | UDS seed base address strap input |
| External | input | 1 | cptra_ss_strap_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i | Prod debug unlock auth PK hash reg bank offset input |
| External | input | 1 | cptra_ss_strap_num_of_prod_debug_unlock_auth_pk_hashes_i | Number of prod debug unlock auth PK hashes input |
| External | input | 1 | cptra_ss_strap_generic_0_i | Generic strap input 0 |
| External | input | 1 | cptra_ss_strap_generic_1_i | Generic strap input 1 |
| External | input | 1 | cptra_ss_strap_generic_2_i | Generic strap input 2 |
| External | input | 1 | cptra_ss_strap_generic_3_i | Generic strap input 3 |
| External | input | 1 | cptra_ss_debug_intent_i | Debug intent signal input |
| External | output | 1 | cptra_ss_dbg_manuf_enable_o | Debug manufacturing enable output |
| External | output | 1 | cptra_ss_cptra_core_soc_prod_dbg_unlock_level_o | SoC production debug unlock level output |
| External | input | 1 | cptra_ss_lc_clk_byp_ack_i | LC clock bypass acknowledge input |
| External | output | 1 | cptra_ss_lc_clk_byp_req_o | LC clock bypass request output |
| External | input | 1 | cptra_ss_lc_ctrl_scan_rst_ni_i | LC controller scan reset input, active low |
| External | input | 1 | cptra_ss_lc_esclate_scrap_state0_i | LC escalate scrap state 0 input |
| External | input | 1 | cptra_ss_lc_esclate_scrap_state1_i | LC escalate scrap state 1 input |
| External | output | 1 | cptra_ss_soc_dft_en_o | SoC DFT enable output |
| External | output | 1 | cptra_ss_soc_hw_debug_en_o | SoC hardware debug enable output |
| External | input | 1 | cptra_ss_fuse_macro_prim_tl_i | Fuse macro primary TL input |
| External | output | 1 | cptra_ss_fuse_macro_prim_tl_o | Fuse macro primary TL output |
| External | input | 1 | cptra_ss_i3c_scl_i | I3C clock input |
| External | input | 1 | cptra_ss_i3c_sda_i | I3C data input |
| External | output | 1 | cptra_ss_i3c_scl_o | I3C clock output |
| External | output | 1 | cptra_ss_i3c_sda_o | I3C data output |
| External | output | 1 | cptra_ss_sel_od_pp_o | Select open-drain push-pull output |
| External | inout | 1 | cptra_ss_i3c_scl_io | I3C clock bidirectional |
| External | inout | 1 | cptra_ss_i3c_sda_io | I3C data bidirectional |
| External | input | 1 | cptra_ss_cptra_core_generic_input_wires_i | Generic input wires for Caliptra core |
| External | input | 1 | cptra_ss_cptra_core_scan_mode_i | Caliptra core scan mode input |
| External | output | 1 | cptra_error_fatal | Fatal error output |
| External | output | 1 | cptra_error_non_fatal | Non-fatal error output |
| External | output | 1 | ready_for_fuses | Ready for fuses output |
| External | output | 1 | ready_for_mb_processing | Ready for mailbox processing output |
| External | output | 1 | mailbox_data_avail | Mailbox data available output |

### Memory Map	/ Address map

### Requirements : Connectivity, Clock & Reset, Constraints & Violations etc

### Programming interface

### Sequences : Reset, Boot,

### How to test : Smoke & more

### Other requirements

## Caliptra Core -

## Integration specification link

# MCU - @Nilesh

### Overview

### Parameters & Defines

### Interface

### Memory Map	/ Address map

### Requirements : Connectivity, Clock & Reset, Constraints & Violations etc

### Programming interface

### Sequences : Reset, Boot,

### How to test : Smoke & more

### Other requirements

# FC Controller - @Emre

### Overview

### Parameters & Defines

### Interface

### Memory Map	/ Address map

### Requirements : Connectivity, Clock & Reset, Constraints & Violations etc

### Programming interface

### Sequences : Reset, Boot,

### How to test : Smoke & more

### Other requirements

# LC Controller - @Emre

### Overview

### Parameters & Defines

### Interface

### Memory Map	/ Address map

### Requirements : Connectivity, Clock & Reset, Constraints & Violations etc

### Programming interface

### Sequences : Reset, Boot,

### How to test : Smoke & more

### Other requirements

# MCI - @Clayton

### Overview

### Parameters & Defines

### Interface

### Memory Map	/ Address map

### Requirements : Connectivity, Clock & Reset, Constraints & Violations etc

### Programming interface

### Sequences : Reset, Boot,

### How to test : Smoke & more

### Other requirements

## I3C core - @Nilesh

### Overview

### Parameters & Defines

### Interface

### Memory Map	/ Address map

### Requirements : Connectivity, Clock & Reset, Constraints & Violations etc

### Programming interface

### Sequences : Reset, Boot,

### How to test : Smoke & more

### Other requirements

## Memories - @Nilesh

### Overview

### Parameters & Defines

### Interface

### Memory Map	/ Address map

### Requirements : Connectivity, Clock & Reset, Constraints & Violations etc

### Programming interface

### Sequences : Reset, Boot,

### How to test : Smoke & more

### Other requirements

## Terminology
## 