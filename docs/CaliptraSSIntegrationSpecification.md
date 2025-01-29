

<div align="center">
  <img src="./images/OCP_logo.png" alt="OCP Logo">
</div>

<h1 align="center"> Caliptra SS Integration Specification v0p8 </h1>

- [1. Scope](#1-scope)
  - [1.1. Document Version](#11-document-version)
  - [1.2. Related specifications](#12-related-specifications)
  - [1.3. Important files \& Path](#13-important-files--path)
- [2. Overview](#2-overview)
- [3. Calpitra SS High level diagram](#3-calpitra-ss-high-level-diagram)
- [4. Integration Considerations](#4-integration-considerations)
  - [4.1. Design Considerations](#41-design-considerations)
  - [4.2. Verification Considerations](#42-verification-considerations)
- [5. Caliptra Subsystem](#5-caliptra-subsystem)
  - [5.1. Parameters](#51-parameters)
  - [5.2. Defines](#52-defines)
  - [5.3. Address map](#53-address-map)
  - [5.4. Interfaces \& Signals](#54-interfaces--signals)
    - [5.4.1. AXI Interface (axi\_if)](#541-axi-interface-axi_if)
    - [5.4.2. Caliptra Subsystem Top Interface \& signals](#542-caliptra-subsystem-top-interface--signals)
  - [5.5. Integration Requirements](#55-integration-requirements)
    - [5.5..1. Clock](#551-clock)
    - [5.5.3. Reset](#553-reset)
  - [5.6. Programming interface](#56-programming-interface)
  - [5.7. Sequences](#57-sequences)
  - [5.8. How to test : Smoke \& more](#58-how-to-test--smoke--more)
  - [5.9. Other requirements](#59-other-requirements)
- [6. Caliptra Core](#6-caliptra-core)
- [7. MCU](#7-mcu)
  - [7.1. Overview](#71-overview)
    - [7.1.1. Parameters \& Defines](#711-parameters--defines)
    - [7.1.2. MCU Top : Interface \& Signals](#712-mcu-top--interface--signals)
- [8. FC Controller - @Emre](#8-fc-controller---emre)
- [9. LC Controller - @Emre](#9-lc-controller---emre)
- [10. MCI - @Clayton](#10-mci---clayton)
- [11. I3C core - @Nilesh](#11-i3c-core---nilesh)
- [12. Memories - @Nilesh](#12-memories---nilesh)
- [13. Terminology](#13-terminology)


# 1. Scope 

<span style="color:red">**Disclaimer**: Internal Draft Document
This document is a work in progress and intended for internal use only. It may contain incomplete or preliminary information subject to change. Do not refer to, share, or rely on this document unless explicitly released in its final version. </span>

For Caliptra Subsystem, this document serves as a hardware integration specification. The scope of this document is to assist integrators in the integration of Caliptra Subsystem. It is not intended to serve as a hardware specification or to include micro-architectural details. This document includes Caliptra Subsystem top-level details along with parameters, defines, interfaces, memory map, programming reference, and guidelines on how to test the integration of the design.

## 1.1. Document Version
<div align="center">

| Date            |   Document Version | Description       |
|-----------------|--------------------|-------------------|
| Jan 31st, 2025  |   v0p8             | Work in progress  |

</div>

## 1.2. Related specifications

The components described in this document are either obtained from open-source GitHub repositories, developed from scratch, or modified versions of open-source implementations. Links to relevant documentation and GitHub sources are shared in the following table.

*Table 1: Related specification and repositories*

| IP/Block      | Code (GitHub URL)                                                         | Documentation (URL)                                                           |
|---------------|---------------------------------------------------------------------------|-------------------------------------------------------------------------------|
| Caliptra-SS   | [GitHub - chipsalliance/caliptra-ss](https://github.com/chipsalliance/caliptra-ss)| [Hardware Specification Document](https://github.com/chipsalliance/caliptra-ss/blob/main/docs/CaliptraSSHardwareSpecification.md)
| Caliptra-rtl  | [GitHub - chipsalliance/caliptra-rtl](https://github.com/chipsalliance/caliptra-rtl)      | [Caliptra RTL documentation](https://github.com/chipsalliance/caliptra-rtl/tree/main/docs) |
| Cores-VeeR    | [GitHub - chipsalliance/Cores-VeeR-EL2](https://github.com/chipsalliance/Cores-VeeR-EL2)  | [VeeR EL2 Programmer’s Reference Manual](http://cores-swerv-el2/RISC-V_SweRV_EL2_PRM.pdf%20at%20master%20%C2%B7) |
| I3C-Core      | [GitHub - chipsalliance/i3c-core](https://github.com/chipsalliance/i3c-core)              | [I3C core documentation](https://github.com/chipsalliance/i3c-core?tab=readme-ov-file#i3c-core) |
| Adams Bridge  | [GitHub - chipsalliance/adams-bridge](https://github.com/chipsalliance/adams-bridge)      | [Adams Bridge Documentation](https://github.com/chipsalliance/adams-bridge/tree/main/docs) |

## 1.3. Important files & Path

| Type | Name | Path |
|------|------|------|
| rtl | Design Top       | [caliptra_ss_top.sv](https://github.com/chipsalliance/caliptra-ss/blob/main/src/integration/rtl/caliptra_ss_top.sv)          |
| tb  | Interconnect Top | [testbench\aaxi4_interconnect.sv](https://github.com/chipsalliance/caliptra-ss/blob/main/src/integration/testbench/aaxi4_interconnect.sv) |
| tb  | Testbench Top    | [testbench\caliptra_ss_top_tb.sv](https://github.com/chipsalliance/caliptra-ss/blob/main/src/integration/testbench/caliptra_ss_top_tb.sv) |

# 2. Overview

The Caliptra Subsystem is designed to provide a robust Root of Trust (RoT) for datacenter-class System on Chips (SoCs), including CPUs, GPUs, DPUs, and TPUs. It integrates both hardware and firmware components to deliver essential security services such as identity establishment, measured boot, and attestation. By incorporating the Caliptra Subsystem, integrators can enhance the security capabilities of their SoCs, providing a reliable RoT that meets industry standards and addresses the evolving security needs of datacenter environments.

# 3. Calpitra SS High level diagram

The following diagram provides a high-level overview of the Caliptra SS subsystem. It illustrates the key components and their interconnections within the system. The diagram includes:

- **Caliptra Core**: The Caliptra Core IP. For more information, see[ Caliptra: A Datacenter System on a Chip (SoC) Root of Trust (RoT)](https://chipsalliance.github.io/Caliptra/doc/Caliptra.html).

- **MCU (Manufactures Control Unit)**: A microcontroller unit that manages various control tasks within the subsystem.

- **I3C Core**: An interface for connecting and communicating with I3C devices, which are used for sensor and peripheral communication.

- **Life Cycle Controller**: A component that manages the different stages of the subsystem's lifecycle, including initialization, operation, and shutdown.

- **Fuse Controller (OTP)**: A one-time programmable memory controller used for storing critical configuration data and security keys.

- **MCI (Memory Controller Interface)**: Manages the communication between the processor and the memory components.

- **Memories**: Various memory components used for storing data and instructions required by the subsystem.

Following high-level diagram helps integrators understand the overall architecture and the relationships between different components within the Caliptra SS subsystem.

![Caliptra Subsystem High Level Diagram](./images/CaliptraSubsystem.png)

# 4. Integration Considerations

By performing these design and verification tasks, the integrator ensures that the Caliptra Subsystem is properly integrated and can function as intended within the larger system.

## 4.1. Design Considerations

1. **Replace the AXI Interconnect**: 
The subsystem utilizes an AXI-based interconnect to facilitate communication between components, with the Caliptra core connecting via an AXI interface. The integrator must replace the default AXI interconnect component with their proprietary interface. This ensures that the subsystem can communicate effectively with the rest of the subsystem components using the integrator's specific interconnect architecture.

2. **Connect the Memories**: The integrator must connect the various memory components required by the subsystem. These memory components are used for storing data and instructions necessary for the operation of the Caliptra SS subsystem.

3. **No Changes to Internals**: Integrators are not expected to make any changes to the internals of the design. The focus should be on ensuring proper integration and connectivity of the subsystem components.

## 4.2. Verification Considerations

1. **Connect the I3C Core GPIO with I3C host Driver**: 
The integrator must connect the I3C core to the appropriate driver for the GPIO pins. This connection is crucial for enabling communication with I3C devices, which are used for communication within the subsystem.

# 5. Caliptra Subsystem

The integration of the Caliptra Subsystem begins with the instantiation of the top-level RTL module, caliptra_ss_top.sv. This module serves as the primary entry point for the subsystem and encapsulates all the logic and components required for the functionality of the Caliptra Root of Trust (RoT). 

All signals must be connected based on the detailed interface and signal descriptions provided in this document. Ensure adherence to the signal direction, width, and functionality to guarantee proper integration with the host SoC.

## 5.1. Parameters 
| Parameter                  | Value | Description                              |
|----------------------------|-------|------------------------------------------|
| ADDR_WIDTH                 | 64    | Address width                            |
| DATA_WIDTH                 | 64    | Data width                               |


## 5.2. Defines

| Define                  | Value | Description                             | 
|-------------------------|-------|-----------------------------------------|
| CLP_CSR_HMAC_KEY_DWORDS | 16    | HMAC Key Dwords                         |
| 

## 5.3. Address map

The following address map is a suggested address map for the given subsystem design. It details the memory layout and the connections between different components within the Caliptra SS subsystem.

| Start Address | End Address | Slave | Name  | Description |
|---|---|---|---|---|
| 64'h1000_0000 | 64'h1000_FFFF | 0 | imem | MCU Instruction memory |
| 64'h2000_4000 | 64'h2000_4FFF | 1 | I3c | I3C Core |
| 64'h8000_0000 | 64'h80FF_FFFF | 2 | n/a | Reserved |
| 64'h3000_0000 | 64'h3FFF_FFFF | 3 | SoC IFC (tb) | SoC / Testbench |
| 64'h2100_0000 | 64'h2200_0000 | 4 | MCI | Memory Controller Interface |
| 64'h7000_0000 | 64'h7000_01FF | 5 | Fuse Ctrl | Fuse Controller |
| 64'h7000_0200 | 64'h7000_03FF | 6 | Fuse Ctrl Core | Fuse Controller Core |
| 64'h7000_0400 | 64'h7000_05FF | 7 | Life Cycle Ctrl | Life Cycle Controller |

## 5.4. Interfaces & Signals

### 5.4.1. AXI Interface (axi_if)

| Signal          | Width                  | Direction (mgr) | Direction (sub) |
|-----------------|------------------------|-----------------|-----------------|
| araddr          | AW                     | output          | input           |
| arburst         | $bits(axi_burst_e)     | output          | input           |
| arsize          | 3                      | output          | input           |
| arlen           | 8                      | output          | input           |
| aruser          | UW                     | output          | input           |
| arid            | IW                     | output          | input           |
| arlock          | 1                      | output          | input           |
| arvalid         | 1                      | output          | input           |
| arready         | 1                      | input           | output          |
| rdata           | DW                     | input           | output          |
| rresp           | $bits(axi_resp_e)      | input           | output          |
| rid             | IW                     | input           | output          |
| rlast           | 1                      | input           | output          |
| rvalid          | 1                      | input           | output          |
| rready          | 1                      | output          | input           |
| awaddr          | AW                     | output          | input           |
| awburst         | $bits(axi_burst_e)     | output          | input           |
| awsize          | 3                      | output          | input           |
| awlen           | 8                      | output          | input           |
| awuser          | UW                     | output          | input           |
| awid            | IW                     | output          | input           |
| awlock          | 1                      | output          | input           |
| awvalid         | 1                      | output          | input           |
| awready         | 1                      | input           | output          |
| wdata           | DW                     | output          | input           |
| wstrb           | DW/8                   | output          | input           |
| wvalid          | 1                      | output          | input           |
| wready          | 1                      | input           | output          |
| wlast           | 1                      | output          | input           |
| bresp           | $bits(axi_resp_e)      | input           | output          |
| bid             | IW                     | input           | output          |
| bvalid          | 1                      | input           | output          |
| bready          | 1                      | output          | input           |

### 5.4.2. Caliptra Subsystem Top Interface & signals 

| Facing   | Type      | width | Signal or Interface Name             | Description                              |
|:---------|:----------|:------|:-------------------------------------|:-----------------------------------------|
| External | input     | 1     | cptra_ss_clk_i                       | Caliptra subsystem clock input           |
| External | input     | 1     | cptra_ss_pwrgood_i                   | Power good signal input                  |
| External | input     | 1     | cptra_ss_rst_b_i                     | Reset signal input, active low           |
| External | axi_if    | na    | cptra_ss_cptra_core_s_axi_if         | Caliptra core AXI sub-interface          |
| External | axi_if    | na    | cptra_ss_cptra_core_m_axi_if         | Caliptra core AXI manager interface      |
| External | axi_if    | na    | cptra_ss_mci_s_axi_if                | Caliptra SS MCI AXI sub-interface        |
| External | axi_if    | na    | cptra_ss_mcu_rom_s_axi_if            | Caliptra SS MCU ROM AXI sub-interface    |
| External | axi_if    | na    | mcu_rom_mem_export_if                | MCU ROM memory export interface          |
| External | axi_if    | na    | cptra_ss_mci_m_axi_if                | Caliptra SS MCI AXI manager interface    |
| External | axi_if    | na    | cptra_ss_mcu_lsu_m_axi_if            | Caliptra SS MCU LSU AXI manager interface|
| External | axi_if    | na    | cptra_ss_mcu_ifu_m_axi_if            | Caliptra SS MCU IFU AXI manager interface|
| External | axi_if    | na    | cptra_ss_i3c_s_axi_if                | Caliptra SS I3C AXI sub-interface        |
| External | input     | na    | cptra_ss_lc_axi_wr_req_i             | LC controller AXI write request input    |
| External | output    | na    | cptra_ss_lc_axi_wr_rsp_o             | LC controller AXI write response output  |
| External | input     | na    | cptra_ss_lc_axi_rd_req_i             | LC controller AXI read request input     |
| External | output    | na    | cptra_ss_lc_axi_rd_rsp_o             | LC controller AXI read response output   |
| External | input     | na    | cptra_ss_otp_core_axi_wr_req_i       | OTP controller AXI write request input   |
| External | output    | na    | cptra_ss_otp_core_axi_wr_rsp_o       | OTP controller AXI write response output |
| External | input     | na    | cptra_ss_otp_core_axi_rd_req_i       | OTP controller AXI read request input    |
| External | output    | na    | cptra_ss_otp_core_axi_rd_rsp_o       | OTP controller AXI read response output  |
| External | input     | 256   | cptra_ss_cptra_obf_key_i             | Caliptra core obfuscation key input      |
| External | input     | CLP_CSR_HMAC_KEY_DWORDS | cptra_ss_cptra_csr_hmac_key_i        | Caliptra core CSR HMAC key input         |
| External | input     | 1     | cptra_ss_cptra_core_jtag_tck_i       | JTAG clock input                         |
| External | input     | 1     | cptra_ss_cptra_core_jtag_tms_i       | JTAG TMS input                           |
| External | input     | 1     | cptra_ss_cptra_core_jtag_tdi_i       | JTAG TDI input                           |
| External | input     | 1     | cptra_ss_cptra_core_jtag_trst_n_i    | JTAG reset input, active low             |
| External | output    | 1     | cptra_ss_cptra_core_jtag_tdo_o       | JTAG TDO output                          |
| External | output    | 1     | cptra_ss_cptra_core_jtag_tdoEn_o     | JTAG TDO enable output                   |
| External | output    | 125   | cptra_ss_cptra_generic_fw_exec_ctrl_o| Generic firmware execution control output|
| External | input     | na    | cptra_ss_lc_ctrl_jtag_i              | LC controller JTAG request input         |
| External | output    | na    | cptra_ss_lc_ctrl_jtag_o              | LC controller JTAG response output       |
| External | interface | na    | cptra_ss_cptra_core_el2_mem_export   | Caliptra core EL2 memory export interface|
| External | output    | 1     | cptra_ss_cptra_core_mbox_sram_cs_o   | Mailbox SRAM chip select output          |
| External | output    | 1     | cptra_ss_cptra_core_mbox_sram_we_o   | Mailbox SRAM write enable output         |
| External | output    | CPTRA_MBOX_ADDR_W | cptra_sscptra_core_mbox_sram_addr_o  | Mailbox SRAM address output              |
| External | output    | CPTRA_MBOX_DATA_AND_ECC_W | cptra_ss_cptra_core_mbox_sram_wdata_o| Mailbox SRAM write data output           |
| External | input     | CPTRA_MBOX_DATA_AND_ECC_W | cptra_ss_cptra_core_mbox_sram_rdata_i| Mailbox SRAM read data input             |
| External | output    | 1     | cptra_ss_cptra_core_imem_cs_o        | Instruction memory chip select output    |
| External | output    | CALIPTRA_IMEM_ADDR_WIDTH | cptra_ss_cptra_core_imem_addr_o      | Instruction memory address output        |
| External | input     | CALIPTRA_IMEM_DATA_WIDTH | cptra_ss_cptra_core_imem_rdata_i     | Instruction memory read data input       |
| External | input     | 1     | cptra_ss_cptra_core_bootfsm_bp_i     | Boot FSM breakpoint input                |
| External | output    | 1     | cptra_ss_cptra_core_etrng_req_o      | External TRNG request output             |
| External | input     | 4     | cptra_ss_cptra_core_itrng_data_i     | Internal TRNG data input                 |
| External | input     | 1     | cptra_ss_cptra_core_itrng_valid_i    | Internal TRNG valid input                |
| External | interface | na    | cptra_ss_mcu_rom_macro_req_if        | MCU ROM macro request interface          |
| External | input     | 32    | cptra_ss_strap_mcu_lsu_axi_user_i    | MCU LSU AXI user strap input             |
| External | input     | 32    | cptra_ss_strap_mcu_ifu_axi_user_i    | MCU IFU AXI user strap input             |
| External | input     | 32    | cptra_ss_strap_clp_axi_user_i        | CLP AXI user strap input                 |
| External | interface | na    | cptra_ss_mci_mcu_sram_req_if         | MCI MCU SRAM request interface           |
| External | interface | na    | cptra_ss_mci_mbox0_sram_req_if       | MCI mailbox 0 SRAM request interface     |
| External | interface | na    | cptra_ss_mci_mbox1_sram_req_if       | MCI mailbox 1 SRAM request interface     |
| External | interface | na    | cptra_ss_mcu0_el2_mem_export         | MCU0 EL2 memory export interface         |
| External | input     | 64    | cptra_ss_mci_generic_input_wires_i   | Generic input wires for MCI              |
| External | input     | 32    | cptra_ss_strap_mcu_reset_vector_i    | MCU reset vector strap input             |
| External | input     | 1     | cptra_ss_mcu_no_rom_config_i         | No ROM configuration input               |
| External | input     | 1     | cptra_ss_mci_boot_seq_brkpoint_i     | MCI boot sequence breakpoint input       |
| External | input     | 1     | cptra_ss_lc_Allow_RMA_on_PPD_i       | Allow RMA on PPD input                   |
| External | output    | 64    | cptra_ss_mci_generic_output_wires_o  | Generic output wires for MCI             |
| External | output    | 1     | cptra_ss_mci_error_fatal_o           | MCI error fatal output                   |
| External | output    | 1     | cptra_ss_mci_error_non_fatal_o       | MCI error non-fatal output               |
| External | input     | 1     | cptra_ss_mcu_jtag_tck_i              | MCU JTAG clock input                     |
| External | input     | 1     | cptra_ss_mcu_jtag_tms_i              | MCU JTAG TMS input                       |
| External | input     | 1     | cptra_ss_mcu_jtag_tdi_i              | MCU JTAG TDI input                       |
| External | input     | 1     | cptra_ss_mcu_jtag_trst_n_i           | MCU JTAG reset input, active low         |
| External | output    | 1     | cptra_ss_mcu_jtag_tdo_o              | MCU JTAG TDO output                      |
| External | output    | 1     | cptra_ss_mcu_jtag_tdoEn_o            | MCU JTAG TDO enable output               |
| External | input     | 64    | cptra_ss_strap_caliptra_base_addr_i  | Caliptra base address strap input        |
| External | input     | 64    | cptra_ss_strap_mci_base_addr_i       | MCI base address strap input             |
| External | input     | 64    | cptra_ss_strap_recovery_ifc_base_addr_i| Recovery interface base address strap input|
| External | input     | 64    | cptra_ss_strap_otp_fc_base_addr_i    | OTP FC base address strap input          |
| External | input     | 64    | cptra_ss_strap_uds_seed_base_addr_i  | UDS seed base address strap input        |
| External | input     | 32    | cptra_ss_strap_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i | Prod debug unlock auth PK hash reg bank offset input |
| External | input     | 32    | cptra_ss_strap_num_of_prod_debug_unlock_auth_pk_hashes_i | Number of prod debug unlock auth PK hashes input |
| External | input     | 32    | cptra_ss_strap_generic_0_i           | Generic strap input 0                    |
| External | input     | 32    | cptra_ss_strap_generic_1_i           | Generic strap input 1                    |
| External | input     | 32    | cptra_ss_strap_generic_2_i           | Generic strap input 2                    |
| External | input     | 32    | cptra_ss_strap_generic_3_i           | Generic strap input 3                    |
| External | input     | 1     | cptra_ss_debug_intent_i              | Debug intent signal input                |
| External | output    | 1     | cptra_ss_dbg_manuf_enable_o          | Debug manufacturing enable output        |
| External | output    | 64    | cptra_ss_cptra_core_soc_prod_dbg_unlock_level_o | SoC production debug unlock level output |
| External | input     | na    | cptra_ss_lc_clk_byp_ack_i            | LC clock bypass acknowledge input        |
| External | output    | na    | cptra_ss_lc_clk_byp_req_o            | LC clock bypass request output           |
| External | input     | 1     | cptra_ss_lc_ctrl_scan_rst_ni_i       | LC controller scan reset input, active low|
| External | input     | 1     | cptra_ss_lc_esclate_scrap_state0_i   | LC escalate scrap state 0 input          |
| External | input     | 1     | cptra_ss_lc_esclate_scrap_state1_i   | LC escalate scrap state 1 input          |
| External | output    | 1     | cptra_ss_soc_dft_en_o                | SoC DFT enable output                    |
| External | output    | 1     | cptra_ss_soc_hw_debug_en_o           | SoC hardware debug enable output         |
| External | input     | na    | cptra_ss_fuse_macro_prim_tl_i        | Fuse macro primary TL input              |
| External | output    | na    | cptra_ss_fuse_macro_prim_tl_o        | Fuse macro primary TL output             |
| External | input     | 1     | cptra_ss_i3c_scl_i                   | I3C clock input                          |
| External | input     | 1     | cptra_ss_i3c_sda_i                   | I3C data input                           |
| External | output    | 1     | cptra_ss_i3c_scl_o                   | I3C clock output                         |
| External | output    | 1     | cptra_ss_i3c_sda_o                   | I3C data output                          |
| External | output    | 1     | cptra_ss_sel_od_pp_o                 | Select open-drain push-pull output       |
| External | inout     | 1     | cptra_ss_i3c_scl_io                  | I3C clock bidirectional                  |
| External | inout     | 1     | cptra_ss_i3c_sda_io                  | I3C data bidirectional                   |
| External | input     | 64    | cptra_ss_cptra_core_generic_input_wires_i | Generic input wires for Caliptra core |
| External | input     | 1     | cptra_ss_cptra_core_scan_mode_i      | Caliptra core scan mode input            |
| External | output    | 1     | cptra_error_fatal                    | Fatal error output                       |
| External | output    | 1     | cptra_error_non_fatal                | Non-fatal error output                   |
| External | output    | 1     | ready_for_fuses                      | Ready for fuses output                   |
| External | output    | 1     | ready_for_mb_processing              | Ready for mailbox processing output      |
| External | output    | 1     | mailbox_data_avail                   | Mailbox data available output            |

## 5.5. Integration Requirements

### 5.5..1. Clock

The `cptra_ss_clk_i` signal is the primary clock input for the Caliptra Subsystem. This signal must be connected to a 100 MHz system clock to ensure proper operation.

- **Signal Name** `cptra_ss_clk_i`
- **Required Frequency** 100 MHz
- **Clock Source** Must be derived from the SoC’s clock generation module or a stable external oscillator.
- **Constraints** 
  - Ensure minimal clock jitter.
  - Maintain a duty cycle close to 50% for optimal performance.
- **Integration Notes**
  
  1. Verify that the SoC or system-level clock source provides a stable 100 MHz clock.
  2. The clock signal must be properly buffered if necessary to meet the subsystem's setup and hold timing requirements.
  3. If a different frequency is required, ensure that a clock divider or PLL is used to generate the 100 MHz clock before connection.

### 5.5.3. Reset
The `cptra_ss_reset_n` signal is the primary reset input for the Caliptra Subsystem. It must be asserted low to reset the subsystem and de-asserted high to release it from reset. Ensure that the reset is held low for a sufficient duration (minimum of 2 clock cycles at 100 MHz) to allow all internal logic to initialize properly.

- **Signal Name:** `cptra_ss_reset_n`
- **Direction:** Input
- **Active Level:** Active-low (`0` resets the subsystem, `1` releases reset)
- **Reset Type:** Synchronous with the `cptra_ss_clk_i` signal
- **Integration Notes:**
  - The reset signal must be synchronized to the 100 MHz `cptra_ss_clk_i` clock to prevent metastability issues.
  - If the reset source is asynchronous, a synchronizer circuit must be used before connecting to the subsystem.
  - During SoC initialization, assert this reset signal until all subsystem clocks and required power domains are stable.

## 5.6. Programming interface



## 5.7. Sequences

    Notes : 
        Reset
        Boot 

Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.

## 5.8. How to test : Smoke & more

Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.

## 5.9. Other requirements

# 6. Caliptra Core

Follow the link for 
[Caliptra Core Integration Specification](https://github.com/chipsalliance/caliptra-rtl/blob/main/docs/CaliptraIntegrationSpecification.md)

# 7. MCU 

## 7.1. Overview

MCU encapusaltes the RISCV instance of Veer Core EL2 instance.

### 7.1.1. Parameters & Defines

### 7.1.2. MCU Top : Interface & Signals

| Facing   | Type           | Width | Name                                 | Description                              |
|----------|----------------|-------|--------------------------------------|------------------------------------------|
| External | input          | 1     | clk                                  | Clock input                              |
| External | input          | 1     | rst_l                                | Reset input, active low                  |
| External | input          | 1     | dbg_rst_l                            | Debug reset input, active low            |
| External | input          | 32    | rst_vec                              | Reset vector input                       |
| External | input          | 1     | nmi_int                              | Non-maskable interrupt input             |
| External | input          | 32    | nmi_vec                              | Non-maskable interrupt vector input      |
| External | output         | 32    | trace_rv_i_insn_ip                   | Trace instruction input                  |
| External | output         | 32    | trace_rv_i_address_ip                | Trace address input                      |
| External | output         | 1     | trace_rv_i_valid_ip                  | Trace valid input                        |
| External | output         | 1     | trace_rv_i_exception_ip              | Trace exception input                    |
| External | output         | 5     | trace_rv_i_ecause_ip                 | Trace exception cause input              |
| External | output         | 1     | trace_rv_i_interrupt_ip              | Trace interrupt input                    |
| External | output         | 32    | trace_rv_i_tval_ip                   | Trace trap value input                   |
| External | mcu_axi_if     | na    | lsu_axi_*                            | LSU AXI interface signals                |
| External | mcu_axi_if     | na    | ifu_axi_*                            | IFU AXI interface signals                |
| External | mcu_axi_if     | na    | sb_axi_*                             | SB AXI interface signals                 |
| External | mcu_axi_if     | na    | dma_axi_*                            | DMA AXI interface signals                |
| External | input          | 1     | lsu_bus_clk_en                       | LSU bus clock enable input               |
| External | input          | 1     | ifu_bus_clk_en                       | IFU bus clock enable input               |
| External | input          | 1     | dbg_bus_clk_en                       | Debug bus clock enable input             |
| External | input          | 1     | dma_bus_clk_en                       | DMA bus clock enable input               |
| External | input          | 1     | timer_int                            | Timer interrupt input                    |
| External | input          | 1     | soft_int                             | Software interrupt input                 |
| External | input          | pt.PIC_TOTAL_INT:1 | extintsrc_req           | External interrupt source request input  |
| External | output         | 1     | dec_tlu_perfcnt0                     | Performance counter 0 toggle output      |
| External | output         | 1     | dec_tlu_perfcnt1                     | Performance counter 1 toggle output      |
| External | output         | 1     | dec_tlu_perfcnt2                     | Performance counter 2 toggle output      |
| External | output         | 1     | dec_tlu_perfcnt3                     | Performance counter 3 toggle output      |
| External | input          | 1     | jtag_tck                             | JTAG clock input                         |
| External | input          | 1     | jtag_tms                             | JTAG TMS input                           |
| External | input          | 1     | jtag_tdi                             | JTAG TDI input                           |
| External | input          | 1     | jtag_trst_n                          | JTAG reset input, active low             |
| External | output         | 1     | jtag_tdo                             | JTAG TDO output                          |
| External | output         | 1     | jtag_tdoEn                           | JTAG TDO enable output                   |
| External | input          | 28    | core_id                              | Core ID input                            |
| External | output         | 1     | mem_clk                              | Memory clock output                      |
| External | output         | pt.ICCM_NUM_BANKS | iccm_clken             | ICCM clock enable output                 |
| External | output         | pt.ICCM_NUM_BANKS | iccm_wren_bank         | ICCM write enable bank output            |
| External | output         | pt.ICCM_NUM_BANKS | iccm_addr_bank         | ICCM address bank output                 |
| External | output         | pt.ICCM_NUM_BANKS | iccm_bank_wr_data      | ICCM bank write data output              |
| External | output         | pt.ICCM_NUM_BANKS | iccm_bank_wr_ecc       | ICCM bank write ECC output               |
| External | input          | pt.ICCM_NUM_BANKS | iccm_bank_dout         | ICCM bank data output                    |
| External | input          | pt.ICCM_NUM_BANKS | iccm_bank_ecc          | ICCM bank ECC output                     |
| External | output         | pt.DCCM_NUM_BANKS | dccm_clken             | DCCM clock enable output                 |
| External | output         | pt.DCCM_NUM_BANKS | dccm_wren_bank         | DCCM write enable bank output            |
| External | output         | pt.DCCM_NUM_BANKS | dccm_addr_bank         | DCCM address bank output                 |
| External | output         | pt.DCCM_NUM_BANKS | dccm_wr_data_bank      | DCCM write data bank output              |
| External | output         | pt.DCCM_NUM_BANKS | dccm_wr_ecc_bank       | DCCM write ECC bank output               |
| External | input          | pt.DCCM_NUM_BANKS | dccm_bank_dout         | DCCM bank data output                    |
| External | input          | pt.DCCM_NUM_BANKS | dccm_bank_ecc          | DCCM bank ECC output                     |
| External | output         | pt.ICACHE_BANKS_WAY | ic_b_sb_wren          | ICache bank way write enable output      |
| External | output         | pt.ICACHE_BANKS_WAY | ic_b_sb_bit_en_vec    | ICache bank way bit enable vector output |
| External | output         | pt.ICACHE_BANKS_WAY | ic_sb_wr_data         | ICache bank way write data output        |
| External | output         | pt.ICACHE_BANKS_WAY | ic_rw_addr_bank_q     | ICache read/write address bank output    |
| External | output         | pt.ICACHE_BANKS_WAY | ic_bank_way_clken_final | ICache bank way clock enable output    |
| External | output         | pt.ICACHE_NUM_WAYS | ic_bank_way_clken_final_up | ICache bank way clock enable up output |
| External | input          | pt.ICACHE_BANKS_WAY | wb_packeddout_pre     | Write-back packed data output            |
| External | input          | pt.ICACHE_NUM_WAYS | wb_dout_pre_up        | Write-back data output up                |
| External | output         | pt.ICACHE_NUM_WAYS | ic_tag_clken_final    | ICache tag clock enable output           |
| External | output         | pt.ICACHE_NUM_WAYS | ic_tag_wren_q         | ICache tag write enable output           |
| External | output         | pt.ICACHE_NUM_WAYS | ic_tag_wren_biten_vec | ICache tag write enable bit vector output|
| External | output         | 26    | ic_tag_wr_data                       | ICache tag write data output             |
| External | output         | pt.ICACHE_INDEX_HI | ic_rw_addr_q          | ICache read/write address output         |
| External | input          | pt.ICACHE_NUM_WAYS | ic_tag_data_raw_pre   | ICache tag data raw output               |
| External | input          | pt.ICACHE_NUM_WAYS | ic_tag_data_raw_packed_pre | ICache tag data raw packed output     |
| External | output         | 1     | iccm_ecc_single_error                | ICCM ECC single error output             |
| External | output         | 1     | iccm_ecc_double_error                | ICCM ECC double error output             |
| External | output         | 1     | dccm_ecc_single_error                | DCCM ECC single error output             |
| External | output         | 1     | dccm_ecc_double_error                | DCCM ECC double error output             |
| External | input          | 1     | mpc_debug_halt_req                   | MPC debug halt request input             |
| External | input          | 1     | mpc_debug_run_req                    | MPC debug run request input              |
| External | input          | 1     | mpc_reset_run_req                    | MPC reset run request input              |
| External | output         | 1     | mpc_debug_halt_ack                   | MPC debug halt acknowledge output        |
| External | output         | 1     | mpc_debug_run_ack                    | MPC debug run acknowledge output         |
| External | output         | 1     | debug_brkpt_status                   | Debug breakpoint status output           |
| External | input          | 1     | i_cpu_halt_req                       | CPU halt request input                   |
| External | output         | 1     | o_cpu_halt_ack                       | CPU halt acknowledge output              |
| External | output         | 1     | o_cpu_halt_status                    | CPU halt status output                   |
| External | output         | 1     | o_debug_mode_status                  | Debug mode status output                 |
| External | input          | 1     | i_cpu_run_req                        | CPU run request input                    |
| External | output         | 1     | o_cpu_run_ack                        | CPU run acknowledge output               |
| External | input          | 1     | scan_mode                            | Scan mode input                          |
| External | input          | 1     | mbist_mode                           | MBIST mode input                         |
| External | input          | 1     | dmi_core_enable                      | DMI core enable input                    |
| External | input          | 1     | dmi_uncore_enable                    | DMI uncore enable input                  |
| External | output         | 1     | dmi_uncore_en                        | DMI uncore enable output                 |
| External | output         | 1     | dmi_uncore_wr_en                     | DMI uncore write enable output           |
| External | output         | 7     | dmi_uncore_addr                      | DMI uncore address output                |
| External | output         | 32    | dmi_uncore_wdata                     | DMI uncore write data output             |
| External | input          | 32    | dmi_uncore_rdata                     | DMI uncore read data input               |
| External | output         | 1     | dmi_active                           | DMI active output                        |


# 8. FC Controller - @Emre

Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.

# 9. LC Controller - @Emre

Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.

# 10. MCI - @Clayton

Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.

# 11. I3C core - @Nilesh

Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.

# 12. Memories - @Nilesh

Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.

# 13. Terminology

| Abbreviation | Description                                                                                      |
| :--------- | :--------- |
| AXI          | Advanced eXtensible Interface, a high-performance, high-frequency communication protocol |
| I3C          | Improved Inter-Integrated Circuit, a communication protocol for connecting sensors and other peripherals. |
| ECC          | Error Correction Code, a method of detecting and correcting errors in data storage and transmission. |
| RISCV        | Reduced Instruction Set Computer Five, an open standard instruction set architecture based on established RISC principles. |                                               |