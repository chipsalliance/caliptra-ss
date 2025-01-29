

<div align="center">
  <img src="./images/OCP_logo.png" alt="OCP Logo">
</div>


<h1 align="center"> Caliptra SS Integration Specification v0p8 </h1>

- [1. Scope](#1-scope)
  - [1.1. Document Version](#11-document-version)
  - [1.2. Related specifications](#12-related-specifications)
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
    - [5.5.1. Clock](#551-clock)
    - [5.5.2. Reset](#552-reset)
    - [5.5.3. Power Good Signal](#553-power-good-signal)
  - [5.6. Programming interface](#56-programming-interface)
  - [5.7. Sequences](#57-sequences)
  - [5.8. How to test](#58-how-to-test)
  - [5.9. Other requirements](#59-other-requirements)
- [6. Caliptra Core](#6-caliptra-core)
- [7. MCU](#7-mcu)
  - [7.1. Overview](#71-overview)
    - [7.1.1. Parameters \& Defines](#711-parameters--defines)
    - [7.1.2. MCU Top : Interface \& Signals](#712-mcu-top--interface--signals)
  - [7.2. Programming interface](#72-programming-interface)
    - [7.2.1. MCU Linker Script Integration](#721-mcu-linker-script-integration)
- [8. FC Controller - @Emre](#8-fc-controller---emre)
- [9. LC Controller - @Emre](#9-lc-controller---emre)
- [10. MCI - @Clayton](#10-mci---clayton)
- [11. I3C core - @Nilesh](#11-i3c-core---nilesh)
- [12. Memories](#12-memories)
    - [List of Memories](#list-of-memories)
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

# 2. Overview

The Caliptra Subsystem is designed to provide a robust Root of Trust (RoT) for datacenter-class System on Chips (SoCs), including CPUs, GPUs, DPUs, and TPUs. It integrates both hardware and firmware components to deliver essential security services such as identity establishment, measured boot, and attestation. By incorporating the Caliptra Subsystem, integrators can enhance the security capabilities of their SoCs, providing a reliable RoT that meets industry standards and addresses the evolving security needs of datacenter environments.

# 3. Calpitra SS High level diagram

The following diagram provides a high-level overview of the Caliptra SS subsystem. It illustrates the key components and their interconnections within the system. The diagram includes:

  - **Caliptra Core**: The Caliptra Core IP. For more information, see[ Caliptra: A Datacenter System on a Chip (SoC) Root of Trust (RoT)](https://chipsalliance.github.io/Caliptra/doc/Caliptra.html).
  - **MCU (Manufactures Control Unit)**: A microcontroller unit that manages various control tasks within the subsystem.
  - **I3C Core**: An interface for connecting and communicating with I3C devices, which are used for sensor and peripheral ommunication.
  - **Life Cycle Controller**: A component that manages the different stages of the subsystem's lifecycle, including initialization, operation, and shutdown.
  - **Fuse Controller (OTP)**: A one-time programmable memory controller used for storing critical configuration data and security keys.
  - **MCI (Memory Controller Interface)**: Manages the communication between the processor and the memory components.
  - **Memories**: Various memory components used for storing data and instructions required by the subsystem.

Following high-level diagram helps integrators understand the overall architecture and the relationships between different components within the Caliptra SS subsystem.

![Caliptra Subsystem High Level Diagram](./images/CaliptraSubsystem.png)

# 4. Integration Considerations

By performing these design and verification tasks, the integrator ensures that the Caliptra Subsystem is properly integrated and can function as intended within the larger system. Several files contain code that may be specific to an integrator's implementation and should be overridden. This overridable code is either configuration parameters with integrator-specific values or modules that implement process-specific functionality. Code in these files should be modified or replaced by integrators using components from the cell library of their fabrication vendor. The following table describes recommended modifications for each file.

| Type | Name | Path |
|------|------|------|
| rtl | Design Top       | [caliptra_ss_top.sv](https://github.com/chipsalliance/caliptra-ss/blob/main/src/integration/rtl/caliptra_ss_top.sv)          |
| tb  | Interconnect Top | [testbench\aaxi4_interconnect.sv](https://github.com/chipsalliance/caliptra-ss/blob/main/src/integration/testbench/aaxi4_interconnect.sv) |
| tb  | Testbench Top    | [testbench\caliptra_ss_top_tb.sv](https://github.com/chipsalliance/caliptra-ss/blob/main/src/integration/testbench/caliptra_ss_top_tb.sv) |

## 4.1. Design Considerations

1. **Replace the AXI Interconnect**: 
The subsystem utilizes an AXI-based interconnect to facilitate communication between components, with the Caliptra core connecting via an AXI interface. The integrator must replace the default AXI interconnect component with their proprietary interface. This ensures that the subsystem can communicate effectively with the rest of the subsystem components using the integrator's specific interconnect architecture.
2. **Connect the Memories**: The integrator must connect the various memory components required by the subsystem. These memory components are used for storing data and instructions necessary for the operation of the Caliptra SS subsystem.
3. **No Changes to Internals**: Integrators are not expected to make any changes to the internals of the design. The focus should be on ensuring proper integration and connectivity of the subsystem components.



## 4.2. Verification Considerations

1. **Connect the I3C Core GPIO with I3C host Driver**: 
The integrator must connect the I3C core to the appropriate driver for the GPIO pins. This connection is crucial for enabling communication with I3C devices, which are used for communication within the subsystem.

# 5. Caliptra Subsystem

The integration of the Caliptra Subsystem begins with the instantiation of the top-level RTL module, caliptra_ss_top.sv. This module serves as the primary entry point for the subsystem and encapsulates all the logic and components required for the functionality of the Caliptra Root of Trust (RoT). All signals must be connected based on the detailed interface and signal descriptions provided in this document. Ensure adherence to the signal direction, width, and functionality to guarantee proper integration with the host SoC.

## 5.1. Parameters 

> Add the location to parameters file

## 5.2. Defines

> Add the location to defines file

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

### 5.5.1. Clock

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

### 5.5.2. Reset

The `cptra_ss_reset_n` signal is the primary reset input for the Caliptra Subsystem. It must be asserted low to reset the subsystem and de-asserted high to release it from reset. Ensure that the reset is held low for a sufficient duration (minimum of 2 clock cycles at 100 MHz) to allow all internal logic to initialize properly.

   - **Signal Name** `cptra_ss_reset_n`
   - **Active Level** Active-low (`0` resets the subsystem, `1` releases reset)
   - **Reset Type** Synchronous with the `cptra_ss_clk_i` signal
   - **Integration Notes**
     - The reset signal must be synchronized to the 100 MHz `cptra_ss_clk_i` clock to prevent metastability issues.
     - If the reset source is asynchronous, a synchronizer circuit must be used before connecting to the subsystem.
     - During SoC initialization, assert this reset signal until all subsystem clocks and required power domains are stable.

### 5.5.3. Power Good Signal 

The `cptra_ss_pwrgood_i` signal serves as an indicator of stable power for the Caliptra Subsystem. When asserted (`1`), it confirms that power is stable and the subsystem can operate normally. When deasserted (`0`), the signal triggers a **hard reset** of the subsystem. Deassertion must be synchronized to `cptra_ss_clk_i` to avoid metastability issues.

  - **Signal Name** `cptra_ss_pwrgood_i`
  - **Active Level** Active-high (`1` indicates stable power, `0` triggers reset)
  - **Assertion Type** Asynchronous  
  - **Deassertion Type** Synchronous to `cptra_ss_clk_i`  
  - **Integration Notes**  
    1. Ensure `cptra_ss_pwrgood_i` is properly generated by the power management unit or system power controller.
    2. Since assertion is asynchronous, it must be immediately driven high once power is stable.
    3. Use a synchronizer to properly align deassertion with `cptra_ss_clk_i` to prevent glitches.
    4. If `cptra_ss_pwrgood_i` remains low, the Caliptra Subsystem will remain in a hard reset state.


## 5.6. Programming interface



## 5.7. Sequences

Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.

## 5.8. How to test



## 5.9. Other requirements

# 6. Caliptra Core

Follow the link for 
[Caliptra Core Integration Specification](https://github.com/chipsalliance/caliptra-rtl/blob/main/docs/CaliptraIntegrationSpecification.md)

# 7. MCU 

## 7.1. Overview

MCU encapusaltes the RISCV instance of Veer Core EL2 instance.

### 7.1.1. Parameters & Defines

> Add the path to MCU parameters and defines.

### 7.1.2. MCU Top : Interface & Signals

> Add the link to MCU top signals.

## 7.2. Programming interface

### 7.2.1. MCU Linker Script Integration

This linker script defines the memory layout for the **Caliptra Subsystem** firmware. It specifies the placement of various sections, ensuring proper memory mapping and execution flow.

> Add path to example linker file.

The following memory regions are defined and must be adhered to during integration:

- **Memory Region Allocation**

  - **DCCM (Data Closely Coupled Memory)**
    - **Base Address:** `0x50000000`
    - **Section:** `.dccm`
    - **Usage:** Used for tightly coupled memory operations.
    - **End Symbol:** `_dccm_end` (marks the end of this region).

  - **Instruction Memory (.text)**
    - **Base Address:** `0x80000000`
    - **Section:** `.text`
    - **Usage:** Stores executable code and functions.
    - **End Symbol:** `_text_end`

  - **Data and Read-Only Sections**
    - **Base Address:** `0x21200000`
    - **Sections:** `.data`, `.rodata`, `.srodata`, `.sbss`
    - **Usage:** Stores initialized data, read-only data, and small uninitialized sections.
    - **End Symbol:** `_data_end`

  - **BSS (Uninitialized Data Section)**
    - **Base Address:** `0x21210000`
    - **Section:** `.bss`
    - **Usage:** Stores uninitialized global and static variables.
    - **End Symbol:** `_bss_end`

  - **Stack Configuration**
    - **Alignment:** 16-byte boundary
    - **Size:** `0x1000` (4 KB)
    - **Usage:** Defines the stack memory location for runtime operations.

  - **I/O Mapped Data Section**
    - **Base Address:** `0x21000410`
    - **Section:** `.data.io`
    - **Usage:** Used for memory-mapped I/O operations.

- **Integration Notes**
  1. **Ensure Proper Memory Mapping:**  
     - The memory layout must match the physical memory configuration of the SoC.
     - If modifications are required, update the base addresses and section placements accordingly.

  2. **Code Placement & Execution:**  
     - The `.text` section starts at `0x80000000` and should be mapped to executable memory.
     - The `_start` entry point must be correctly set to align with boot ROM execution.

  3. **Data and Stack Placement Considerations:**  
     - The `.bss` and `.data` sections should be properly initialized by the runtime startup code.
     - The stack must be correctly set up before function execution to avoid memory corruption.

  4. **I/O Mapped Data Handling:**  
     - The `.data.io` section at `0x21000410` is used for memory-mapped peripherals.  
     - Ensure correct access permissions are configured in the memory controller.

By following this linker script configuration, the firmware can be correctly mapped and executed within the **Caliptra Subsystem**.

# 8. FC Controller - @Emre

Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.

# 9. LC Controller - @Emre

Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.

# 10. MCI - @Clayton

Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.

# 11. I3C core - @Nilesh

Documentation : https://github.com/chipsalliance/i3c-core/blob/main/docs/source/top.md 

- Connections
  - Connection to AXI interface
  - GPIO connection to I3C Host (VIP or RTL)
- Two target device 
  - Recovery Target 
  - General Target
- Programming sequence
  - Programming sequence from AXI side to initialize the device
  - Programming sequence from GPIO side 
- Execution 
  - CCC commands to program dynamic address for both the targets
  - Read the dynamic Address for each target
- Smoke test
  - Program & Read Recovery interface registers
  - Write and read TTI interface from each side.

# 12. Memories 

### List of Memories

| **Memory Category**                     | **Memory Name**                         | **Interface**                                    | **Size**           | **Access Type**   | **Description**                                             |
|-----------------------------------------|-----------------------------------------|--------------------------------------------------|--------------------|-------------------|-------------------------------------------------------------|
| **Caliptra SS MCU0**                    | **Instruction ROM**                     | `mcu_rom_mem_export_if`                          | TBD                | Read-Only         | Stores the instructions for MCU0 execution                   |
| **Caliptra SS MCU0**                    | **Memory Export**                       | `cptra_ss_mcu0_el2_mem_export`                   | TBD                | Read/Write        | Memory export for MCU0 access                               |
| **Caliptra SS MCU0**                    | **Shared Memory (SRAM)**                | `cptra_ss_mci_mcu_sram_req_if`                   | TBD                | Read/Write        | Shared memory between MCI and MCU for data storage           |
| **Caliptra SS MBOX**                   | **MBOX0 Memory**                        | `cptra_ss_mci_mbox0_sram_req_if`                 | TBD                | Read/Write        | Memory for MBOX0 communication                               |
| **Caliptra SS MBOX**                   | **MBOX1 Memory**                        | `cptra_ss_mci_mbox1_sram_req_if`                 | TBD                | Read/Write        | Memory for MBOX1 communication                               |
| **Caliptra Core**                       | **ICCM, DCCM IF**                       | `cptra_ss_cptra_core_el2_mem_export`             | TBD                | Read/Write        | Interface for the Instruction and Data Closely Coupled Memory (ICCM, DCCM) of the core |
| **Caliptra Core**                       | **IFU (Instruction Fetch Unit)**        | `cptra_ss_mcu_rom_macro_req_if`                  | TBD                | Read-Only         | Interface for instruction fetch unit (IFU)                   |




# 13. Terminology

| Abbreviation | Description                                                                                      |
| :--------- | :--------- |
| AXI          | Advanced eXtensible Interface, a high-performance, high-frequency communication protocol |
| I3C          | Improved Inter-Integrated Circuit, a communication protocol for connecting sensors and other peripherals. |
| ECC          | Error Correction Code, a method of detecting and correcting errors in data storage and transmission. |
| RISCV        | Reduced Instruction Set Computer Five, an open standard instruction set architecture based on established RISC principles. |                                               |