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

The Fuse Controller is a core component in the secure infrastructure of the system, responsible for managing the fuses and ensuring the integrity, consistency, and secure storage of sensitive data. It provides essential interfaces for direct fuse programming. The Fuse Controller interacts closely with the Lifecycle Controller (LC), FUSE macros, MCI, and Caliptra-core.

For an in-depth understanding of the Fuse Controller's functionality, including its programming flow, refer to [Caliptra Subsystem Hardware Specification Document](CaliptraSSHardwareSpecification.md).
### Parameters & Defines

| Parameter                | Default                        | Description                                         |
|--------------------------|--------------------------      |-----------------------------------------------------|
| `AlertAsyncOn`           | 5                              | Enables asynchronous transitions on alerts.         |
| `MemInitFile`            | `""`                           | Hex file to initialize the OTP macro, including ECC.|

---

### Interface

| Facing     | Type       | Width   | Name                          | External Name in SoC Level        | Description                                            |
|------------|------------|-------  |-------------------------------|-----------------------------------|--------------------------------------------------------|
| External   | Input      | 1       | `clk_i`                       | `cptra_ss_clk_i`                  | Fuse Controller clock input.                          |
| External   | Input      | 1       | `rst_ni`                      | `cptra_ss_rst_b_i`                | Reset signal input, active low.                       |
| External   | interface  | 1       | `core_axi_wr_req`             | `cptra_ss_otp_core_axi_wr_req_i`  | AXI write request.                         |
| External   | interface  | 1       | `core_axi_wr_rsp`             | `cptra_ss_otp_core_axi_wr_rsp_o`  | AXI write response.                          |
| External   | interface  | 1       | `core_axi_rd_req`             | `cptra_ss_otp_core_axi_rd_req_i`  | AXI read request.                          |
| External   | interface  | 1       | `core_axi_rd_rsp`             | `cptra_ss_otp_core_axi_rd_rsp_o`  | AXI read response.                           |
| External   | interface  | 1       | `prim_tl_i`                   | `cptra_ss_fuse_macro_prim_tl_i`   | Input to the Fuse Macro's primitive TL interface.                                                |
| External   | interface  | 1       | `prim_tl_o`                   | `cptra_ss_fuse_macro_prim_tl_o`   | Output from the Fuse Macro's primitive TL interface.                                             |
| Internal   | Output     | 1       | `intr_otp_operation_done_o`   |                                   | Indicates that the OTP operation has completed.                                                  |
| Internal   | Output     | 1       | `intr_otp_error_o`            |                                   | OTP error interrupt output (to be connected to MCI).                                             |
| Internal   | Output     | 5       | `alerts`                      |                                   | Alert signals for critical errors.                                                               |
| Internal   | Input      | 1       | `pwr_otp_i`                   |                                   | OTP initialization request from the power manager.                                               |
| Internal   | Output     | Struct  | `pwr_otp_o`                   |                                   | OTP response to the power manager.                                                               |
| Internal   | Input      | Struct  | `lc_otp_vendor_test_i`        |                                   | Vendor test request input from LC Controller.                                                    |
| Internal   | Output     | Struct  | `lc_otp_vendor_test_o`        |                                   | Vendor test response to LC Controller.                                                           |
| Internal   | Input      | Struct  | `lc_otp_program_i`            |                                   | Lifecycle OTP programming request from LC Controller.                                            |
| Internal   | Output     | Struct  | `lc_otp_program_o`            |                                   | Lifecycle OTP programming response to LC Controller.                                             |
| Internal   | Input      | 1       | `lc_dft_en_i`                 |                                   | DFT enable input from LC Controller.                                                             |
| Internal   | Input      | 1       | `lc_escalate_en_i`            |                                   | Escalation enable input from LC Controller.                                                      |
| Internal   | Input      | 1       | `lc_check_byp_en_i`           |                                   | Clock bypass check enable input from LC Controller.                                              |
| Internal   | Output     | Struct  | `otp_lc_data_o`               |                                   | Lifecycle broadcasted data output to LC Controller.                                              |
| Internal   | Output     | Struct  | `otp_broadcast_o`             |                                   | FUSE broadcast output to Caliptra-core. This port broadcasts UDS and Field-entropy.             |


### Memory Map	/ Address map


See [Fuse Controller Register Map](../src/fuse_ctrl/doc/registers.md).

---

### Requirements: Connectivity, Clock & Reset, Constraints & Violations

1. **Connectivity**:
   - The Fuse Controller must interface seamlessly with the Fuse Macros, ensuring proper ECC support during programming and read operations.
   - All AXI interfaces (`core_axi_wr_req`, `core_axi_rd_req`) must follow the protocol specifications.
   - Inputs like `lc_otp_program_i` and `pwr_otp_i` should connect properly to the Lifecycle Controller (LC) and MCI respectively.
   - Alerts must propagate correctly to the system's alert manager for error handling.

2. **Constraints & Violations**:
   - Any access to fuses must be gated by the `FUSE_CTRL_DIRECT_ACCESS_REGWEN` bit to prevent unauthorized writes.
   - Timeout conditions during consistency checks (`FUSE_CTRL_CHECK_TIMEOUT`) should trigger appropriate alerts.
   - Errors like invalid data, ECC failures, or access violations should raise alerts via the `alerts` signal.

---

### Programming interface
The programming interface for the Fuse Controller (FC) is designed to manage lifecycle states, handle fuses with ECC support, and ensure secure interactions with the Fuse Macros. Below are the key operations supported by the programming interface:

1. **Direct Access Interface (DAI)**:
   - **Registers**:
     - `FUSE_CTRL_DIRECT_ACCESS_CMD`: Specifies the operation (`FUSE_CTRL_CMD_DAI_WRITE` for write, `FUSE_CTRL_CMD_DAI_READ` for read).
     - `FUSE_CTRL_DIRECT_ACCESS_ADDRESS`: Specifies the fuse memory address to access.
     - `FUSE_CTRL_DIRECT_ACCESS_WDATA_0`: Write data (32-bit granularity).
     - `FUSE_CTRL_DIRECT_ACCESS_WDATA_1`: Write data for 64-bit operations.
     - `FUSE_CTRL_DIRECT_ACCESS_RDATA_0`: Read data (32-bit granularity).
     - `FUSE_CTRL_DIRECT_ACCESS_RDATA_1`: Read data for 64-bit operations.
   - **Procedure**:
     - Write the address to `FUSE_CTRL_DIRECT_ACCESS_ADDRESS`.
     - For write operations:
       - Populate `FUSE_CTRL_DIRECT_ACCESS_WDATA_0` (and `FUSE_CTRL_DIRECT_ACCESS_WDATA_1` for 64-bit operations).
     - Set the command in `FUSE_CTRL_DIRECT_ACCESS_CMD`.
     - Wait for the operation to complete by polling the `DAI_IDLE` bit in `FUSE_CTRL_STATUS`.
   - **ECC Support**:
     - ECC is automatically applied during programming to ensure data integrity.

2. **Digest Calculation**:
   - Used to lock a partition after programming is complete.
   - **Registers**:
     - `FUSE_CTRL_DIRECT_ACCESS_CMD`: Use command `0x4` for digest calculation.
     - `FUSE_CTRL_DIRECT_ACCESS_ADDRESS`: Partition base address.
   - **Procedure**:
     - Write the partition base address to `FUSE_CTRL_DIRECT_ACCESS_ADDRESS`.
     - Trigger the digest calculation command (`0x4`) in `FUSE_CTRL_DIRECT_ACCESS_CMD`.
     - Poll the `DAI_IDLE` bit in `FUSE_CTRL_STATUS` to confirm the operation is complete.
---

### Sequences: Reset, Boot

1. **Reset Sequence**:
   - De-assert `rst_ni` after the primary clock (`clk_i`) stabilizes.
   - Verify reset state by reading `FUSE_CTRL_STATUS`. All errors in the status register should be 0.
   - Ensure Fuse Macros are in their default state after reset.

2. **Boot Sequence**:
   - Initialize Fuse Macros by programming essential fuses using the programming interface.
   - Perform a full integrity check by triggering `FUSE_CTRL_CHECK_TRIGGER` and ensure the system is error-free before proceeding.
   - Validate readiness by checking the `FUSE_CTRL_STATUS` register.

---

### How to test : Smoke & more
The smoke test focuses on ensuring basic functionality and connectivity of the FC & LCC.
**TODO** More details will be provided once FC is ready to test.

# LC Controller - @Emre

### Overview

The LC Controller (Lifecycle Controller) is a critical component of the Caliptra Subsystem, responsible for securely managing the lifecycle states of the chip. The LC Controller interacts with other subsystems such as the Fuse Controller, MCI, AXI interconnect, and JTAG TAP to enforce secure transitions, validate tokens, and generate error conditions. Additionally, it implements escalation mechanisms to respond to security breaches, enabling the chip to enter secure states like SCRAP.

For a detailed description of the Lifecycle Controller's architecture, design, and operational flow, refer to [Caliptra Subsystem Hardware Specification Document](CaliptraSSHardwareSpecification.md).

### Parameters & Defines

Parameter                        | Default (Max)  | Description
---------------------------------|----------------|---------------
`AlertAsyncOn`                   | 2'b11          |
`IdcodeValue`                    | `32'h00000001` | Idcode for the LC JTAG TAP.
`RndCnstLcKeymgrDivInvalid`      | (see RTL)      | Diversification value used for all invalid life cycle states.
`RndCnstLcKeymgrDivTestUnlocked` | (see RTL)      | Diversification value used for the TEST_UNLOCKED* life cycle states.
`RndCnstLcKeymgrDivDev`          | (see RTL)      | Diversification value used for the DEV life cycle state.
`RndCnstLcKeymgrDivProduction`   | (see RTL)      | Diversification value used for the PROD/PROD_END life cycle states.
`RndCnstLcKeymgrDivRma`          | (see RTL)      | Diversification value used for the RMA life cycle state.

### Interface


Facing      | Type       | width  | Name                  |  External Name in SoC Level         | Description   |
------------|:-----------|:-------|:----------------------|:------------------------------------|:-------       |
External    |input       |   1    | `clk_i`               | `cptra_ss_clk_i`                    | clock         |
External    |input       |   1    | `rst_ni`              | `cptra_ss_rst_b_i`                  | LC controller reset input, active low|
External    |input       |   1    | `Allow_RMA_on_PPD`    | `cptra_ss_lc_Allow_RMA_on_PPD_i`    | This is GPIO strap pin. This pin should be high until LC completes its state transition to RMA.|
External    |interface   |   1    | `axi_wr_req`          | `cptra_ss_lc_axi_wr_req_i`          | LC controller AXI write request input |
External    |interface   |   1    | `axi_wr_rsp`          | `cptra_ss_lc_axi_wr_rsp_o`          | LC controller AXI write response output|
External    |interface   |   1    | `axi_rd_req`          | `cptra_ss_lc_axi_rd_req_i`          | LC controller AXI read request input |
External    |interface   |   1    | `axi_rd_rsp`          | `cptra_ss_lc_axi_rd_rsp_o`          | LC controller AXI read response output |
External    |interface   |   1    | `jtag_i`              | `cptra_ss_lc_ctrl_jtag_i`           | LC controller JTAG input ports  |
External    |interface   |   1    | `jtag_o`              | `cptra_ss_lc_ctrl_jtag_o`           | LC controller JTAG output ports|
External    |input       |   1    | `scan_rst_ni`         | `cptra_ss_lc_ctrl_scan_rst_ni_i`    | LC controller scan reset input, active low|
Internal    |output      |   3    | `alerts`              |                                     | Alert outputs generated by LCC if there is an error due to one of following: register bus, lc state and fuse programming |
External    |input       |   1    | `esc_scrap_state0`    | `cptra_ss_lc_esclate_scrap_state0_i`| An escalation input that leads LC controller to enter into SCRAP mode  |
External    |input       |   1    | `esc_scrap_state1`    | `cptra_ss_lc_esclate_scrap_state1_i`| An escalation input that eads LC controller to enter into SCRAP mode  |
Internal    |input       |   1    | `pwr_lc_i`            |                                     | A power initilization input coming from MCI |
Internal    |struct      |   1    | `pwr_lc_o`            |                                     | Two outputs show: (i) LC controller can accept a request, (ii) LC is initialized. |
Internal    |struct      |   1    | `lc_otp_vendor_test_o`|                                     | Access to fuse controller for vendor test partitions |
Internal    |struct      |   1    | `lc_otp_vendor_test_i`|                                     | Access to fuse controller for vendor test partitions |
Internal    |struct      |   1    | `lc_otp_program_o`    |                                     | Programming interface to fuse controller to update LCC state and couter |
Internal    |struct      |   1    | `lc_otp_program_i`    |                                     | Programming interface from fuse controller to update LCC state and couter |
Internal    |struct      |   1    | `otp_lc_data_i`       |                                     | Broadcasted values from the fuse controller |
Internal    |output      |   1    | `lc_dft_en_o`         |                                     | DFT enable to MCI |
Internal    |output      |   1    | `lc_hw_debug_en_o`    |                                     | CLTAP enable to MCI |
Internal    |output      |   1    | `lc_escalate_en_o`    |                                     | Broadcast signal to promote esclation in SoC |
Internal    |output      |   1    | `lc_check_byp_en_o`   |                                     | External clock status delivery signal to fuse controller |
External    |output      |   1    | `lc_clk_byp_req_o`    | `cptra_ss_lc_clk_byp_req_o`         | A request port to swtich from LCC clock to external clock |
External    |input       |   1    | `lc_clk_byp_ack_i`    | `cptra_ss_lc_clk_byp_ack_i`         | Acknowledgment signal to indicate external clock request is accepted              |
Internal    |input       |   1    | `otp_device_id_i`     |                                     | Fuse device ID              |
Internal    |input       |   1    | `otp_manuf_state_i`   |                                     | Fuse manufacturing ID               |
Internal    |output      |   1    | `hw_rev_o`            |                                     | Reflection of HW revision ID read from fuse controller              |


### Memory Map / Address Map

See LC Controller Register Map**TODO: link will be provided**.
<!-- Register Offset                             | Description                                           | Address
-----------------------------------------   |:------------------------------------------------------|:------    |                                         
`LC_CTRL_ALERT_TEST_OFFSET`                 | Alert test register                                   |   0x0   |         
`LC_CTRL_STATUS_OFFSET`                     | Status register                                       |   0x4   |     
`LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_OFFSET` | Claim transition interface write-enable register      |   0x8   |                                         
`LC_CTRL_CLAIM_TRANSITION_IF_OFFSET`        | Claim transition interface register                   |   0xc   |                         
`LC_CTRL_TRANSITION_REGWEN_OFFSET`          | Transition write-enable register                      |   0x10  |                     
`LC_CTRL_TRANSITION_CMD_OFFSET`             | Transition command register                           |   0x14  |                 
`LC_CTRL_TRANSITION_CTRL_OFFSET`            | Transition control register                           |   0x18  |                 
`LC_CTRL_TRANSITION_TOKEN_0_OFFSET`         | Transition token register (part 0)                    |   0x1c  |                         
`LC_CTRL_TRANSITION_TOKEN_1_OFFSET`         | Transition token register (part 1)                    |   0x20  |                         
`LC_CTRL_TRANSITION_TOKEN_2_OFFSET`         | Transition token register (part 2)                    |   0x24  |                         
`LC_CTRL_TRANSITION_TOKEN_3_OFFSET`         | Transition token register (part 3)                    |   0x28  |                         
`LC_CTRL_TRANSITION_TARGET_OFFSET`          | Transition target register                            |   0x2c  |                 
`LC_CTRL_OTP_VENDOR_TEST_CTRL_OFFSET`       | OTP vendor test control register                      |   0x30  |                     
`LC_CTRL_OTP_VENDOR_TEST_STATUS_OFFSET`     | OTP vendor test status register                       |   0x34  |                     
`LC_CTRL_LC_STATE_OFFSET`                   | Life cycle state register                             |   0x38  |                 
`LC_CTRL_LC_TRANSITION_CNT_OFFSET`          | Life cycle transition count register                  |   0x3c  |                         
`LC_CTRL_LC_ID_STATE_OFFSET`                | Life cycle ID state register                          |   0x40  |                 
`LC_CTRL_HW_REVISION0_OFFSET`               | Hardware revision register (part 0)                   |   0x44  |                         
`LC_CTRL_HW_REVISION1_OFFSET`               | Hardware revision register (part 1)                   |   0x48  |                         
`LC_CTRL_DEVICE_ID_0_OFFSET`                | Device ID register (part 0)                           |   0x4c  |                 
`LC_CTRL_DEVICE_ID_1_OFFSET`                | Device ID register (part 1)                           |   0x50  |                 
`LC_CTRL_DEVICE_ID_2_OFFSET`                | Device ID register (part 2)                           |   0x54  |                 
`LC_CTRL_DEVICE_ID_3_OFFSET`                | Device ID register (part 3)                           |   0x58  |                 
`LC_CTRL_DEVICE_ID_4_OFFSET`                | Device ID register (part 4)                           |   0x5c  |                 
`LC_CTRL_DEVICE_ID_5_OFFSET`                | Device ID register (part 5)                           |   0x60  |                 
`LC_CTRL_DEVICE_ID_6_OFFSET`                | Device ID register (part 6)                           |   0x64  |                 
`LC_CTRL_DEVICE_ID_7_OFFSET`                | Device ID register (part 7)                           |   0x68  |                 
`LC_CTRL_MANUF_STATE_0_OFFSET`              | Manufacturing state register (part 0)                 |   0x6c  |                             
`LC_CTRL_MANUF_STATE_1_OFFSET`              | Manufacturing state register (part 1)                 |   0x70  |                             
`LC_CTRL_MANUF_STATE_2_OFFSET`              | Manufacturing state register (part 2)                 |   0x74  |                             
`LC_CTRL_MANUF_STATE_3_OFFSET`              | Manufacturing state register (part 3)                 |   0x78  |                             
`LC_CTRL_MANUF_STATE_4_OFFSET`              | Manufacturing state register (part 4)                 |   0x7c  |                             
`LC_CTRL_MANUF_STATE_5_OFFSET`              | Manufacturing state register (part 5)                 |   0x80  |                             
`LC_CTRL_MANUF_STATE_6_OFFSET`              | Manufacturing state register (part 6)                 |   0x84  |                             
`LC_CTRL_MANUF_STATE_7_OFFSET`              | Manufacturing state register (part 7)                 |   0x88  |                              -->

### Requirements: Connectivity, Clock & Reset, Constraints & Violations

1. **Connectivity**:
   - Ensure proper routing of all signals to avoid conflicts with other modules.
   - Interfaces like `jtag` and `axi` must adhere to the defined protocol specifications.
   - Esclation signals (`esc_scrap_state0` and `esc_scrap_state1`) brings LC controller into SCRAP mode and therefore needs to be connected to a dedicated controller.
   - `Allow_RMA_on_PPD` needs to be tied 0 if it is not being used. Otherwise, it might break LC controller's internal FSM.
   - Avoid glitches on `Allow_RMA_on_PPD` and escalation inputs (`esc_scrap_state0`, `esc_scrap_state1`) that could cause unintended transitions.
   - Verify that all output signals, including alerts, remain within the expected ranges under normal operation.

### Programming Interface

The LC Controller's programming interface facilitates lifecycle state transitions, secure token authentication, and system initialization. Below are the key programming steps:

1. **Initialization**:
   - Ensure the LC Controller is ready by polling the `LC_CTRL_STATUS_OFFSET` register for the `READY_MASK` bit.
   - Verify initialization is complete using the `INIT_MASK` bit in the same register.
   - Corresponding fuse partitions need to be provisioned in order to perform state transitions

2. **Lifecycle State Transitions**:
   - Claim the transition mutex by writing `0x96` (MuBi8True) to `LC_CTRL_CLAIM_TRANSITION_IF_OFFSET` and polling until the value is correctly latched.
   - Set the desired next lifecycle state by writing to `LC_CTRL_TRANSITION_TARGET_OFFSET`.
   - Write the 128-bit transition token (if required) into the `LC_CTRL_TRANSITION_TOKEN_*_OFFSET` registers.
   - Trigger the state transition by writing `0x1` to `LC_CTRL_TRANSITION_CMD_OFFSET`.
   - Poll the `LC_CTRL_STATUS_OFFSET` register to monitor for successful state transition or detect errors such as token errors, OTP errors, or RMA strap violations.

3. **Token Validation**:
   - For conditional state transitions, provide the transition token before the transition request.

4. **RMA Strap Handling**:
   - Ensure the `Allow_RMA_on_PPD` GPIO strap is asserted for RMA transitions. Transitions without this strap will fail with an appropriate status in the `LC_CTRL_STATUS_OFFSET` register.

---

### Sequences: Reset, Boot

1. **Reset Sequence**:
   - Bring the LC Controller out of reset by asserting and de-asserting `rst_ni` after clock stabilization.
   - Perform a reset sequence after each state transition routine

2. **Boot Sequence**:
   - Enable MCI that intilaize the LC controller.
   - Verify successful initialization by reading `LC_CTRL_STATUS_OFFSET`.

4. **Error Scenarios**:
   - Test scenarios where invalid tokens, Fuse errors, or missing RMA straps are injected to validate error handling and system recovery mechanisms.

---

### How to Test: Smoke & More

#### Smoke Test
1. **Basic Connectivity**:
   - Verify the LC Controller responds to read and write operations on key registers (e.g., `LC_CTRL_STATUS_OFFSET`, `LC_CTRL_CLAIM_TRANSITION_IF_OFFSET`).

2. **Basic Initialization**:
   - Check that the `READY_MASK` and `INIT_MASK` bits in `LC_CTRL_STATUS_OFFSET` transition to the expected values during initialization.

3. **Lifecycle Transition**:
   - Perform a single state transition (e.g., `RAW` to `TEST_UNLOCKED0`)

#### Functional Tests
1. **Full Lifecycle Sequence**:
   - Run all lifecycle transition functions and validate each transition step via the status register and debug messages.

2. **Error Injection**:
   - Test token errors by providing invalid tokens during a transition request.
   - Simulate OTP errors by corrupting OTP data or configuration.
   - Test RMA transitions with and without the `Allow_RMA_on_PPD` GPIO strap.

3. **Boundary Testing**:
   - Verify correct operation under boundary conditions, such as repeated transitions, simultaneous requests, or rapid reset sequences.

#### Advanced Tests
1. **Stress Test**:
   - Perform rapid transitions through multiple lifecycle states to validate system robustness.
   - Simulate power interruptions during critical operations.

2. **Integration Tests**:
   - Verify interaction with other modules such as the fuse controller and MCI during state transitions.




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