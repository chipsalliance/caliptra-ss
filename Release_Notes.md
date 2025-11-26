# **Release Notes** #

## Caliptra Subsystem 2p1p1 Release notes
_*Release Date: 2025/11/26*_

Integration spec updates with several clarifications

### 1. Caliptra Core
- Upgraded to Caliptra Core 2.1.1 final release that includes:
  - Fix for security state debug not unlocking after manuf/prod dbg unlock flow (#1132)
  - Fix for bug #1118 from ABR and test case to validate (#1121)

### 2. I3C
- Upgraded I3C to v1p4-patch at commit 4f2bb875e50752c3dfef9396f0dcf80be7316269
  - Numerous fixes for CCC commands, CDC signals, virtual addressing, IBIs, min frequency, assorted FIXME items

### 3. Life Cycle Controller (LCC)
- No changes

### 4. Fuse Controller (FC)
- UDS/FE Programming limitation in debug mode (#953)

### 5. Manufacturer Control Interface (MCI):
- No changes

### Validation test plan completed for:
- FIPS Zeroization
- OCP LOCK



# Previous Releases #

## Caliptra Subsystem 2p1 Release notes
_*Release Date: 2025/10/12*_

Integration spec updates for OCP LOCK and FIPS Zeroization 

### 1. Caliptra Core
- Upgraded to Caliptra Core 2.1 final release that includes OCP LOCK, MLKEM, AES DMA, Reduced MBOX SRAM, Improvements of KV

### 2. I3C
- AXI streaming boot support in I3C; upgraded I3C to v1p4

### 3. Life Cycle Controller (LCC)
- VolatileRawUnlockEn control for SOC as a strap

### 4. Fuse Controller (FC)
- FIPS Zeroization required changes and fuse map updates for OCP LOCK Ratched seeds

### 5. Manufacturer Control Interface (MCI):
- No changes

### Validation test plan completed for:
- FIPS Zeroization
- OCP LOCK



## Caliptra 2.1 Subsystem 1p0 RC1 Release notes
_*Release Date: 2025/09/07*_

Integration spec updates for OCP LOCK and FIPS Zeroization 

### 1. Caliptra Core
- Upgraded to Caliptra Core 2.1 RC1 that includes OCP LOCK, MLKEM, AES DMA, Reduced MBOX SRAM, Improvements of KV

### 2. I3C
- AXI streaming boot support into I3C; upgraded I3C to newer revision

### 3. Life Cycle Controller (LCC)
- VolatileRawUnlockEn control for SOC as a strap

### 4. Fuse Controller (FC)
- FIPS Zeroization required changes and fuse map updates for OCP LOCK Ratched seeds

### 5. Manufacturer Control Interface (MCI):
- No changes

### Validation test plan completed for:
- FIPS Zeroization
- OCP LOCK



## Caliptra 2.0 Subsystem 1p0 Release notes
_*Release Date: 2025/04/30*_

HW & Integration spec updates coverage all the modules

### 1. Caliptra Core
- Upgraded to Caliptra Core 2.0 release
- Subsystem Flow Validation 
  - Production debug unlock flow
  - Manufacturing debug unlock flow
  - Streaming boot
  - UDS programming sequence with directed tests
  - Production Caliptra Core ROM

### 2. I3C
- Added support for more CCCs as part of target controller
- Added interrupt support 
- Validated various subsystem interactions
- Coverage analysis and bug fixes
- FPGA validation of I3C
- Compatibility test suite validation of the target mode (Review I3C [README](https://github.com/chipsalliance/i3c-core/blob/v1p0/README.md))

### 3. Life Cycle Controller (LCC)
- LCC validation & Coverage analysis
- Subsystem HW & Integration spec updates

### 4. Fuse Controller (FC)
- Final fuse map created per architectural requirements
- Automation/Scripts to generate/update partitions per SOC specific needs and to generate corresponding vmem files for validation
- Added extended vendor PK hash support with volatile locking
- Added Zeroization for UDS-seed and Field Entropy
- FC validation & Coverage analysis
- Subsystem HW & Integration spec updates

### 5. Manufacturer Control Interface (MCI):
- WDT & RISC-V MTIMER
- Trace Buffer
- JTAG Security Controls
- Interrupt Aggregation support
- MCI Validation & Coverage Analysis

### Validation test plan completed for:
- Streaming Boot flow over I3C
- DMA from Caliptra to/from MCI, Fuse Controller, I3C
- MCU interaction with all the blocks (I3C, Caliptra, LCC, FC, MCU ROM, and MCI)
- Life Cycle Controller interactions and life cycle state changes
- Life Cycle Controller & Fuse Controller interactions

## Caliptra Subsystem 0.8 Release Notes
_*Release Date: 2025/01/20*_

### 1. Caliptra Core
- Adams Bridge
- PQC Key Vault & Derivation Support
- OCP Recovery Support
- Updated VeeR core pointing to VeeR 2.0 release
- Increased ROM, ICCM/DCCM, and Mailbox sizes for Caliptra 2.0
- Manufacturing Debug Unlock Support
- Production Debug Unlock Support
- All bug fixes since Caliptra core freeze

### 2. I3C
- Compliant with:
  - MIPI Alliance Specification for I3C Basic, Version 1.1.1
  - MIPI Alliance Specification for I3C HCI, Version 1.2
  - MIPI Alliance Specification for I3C TCRI, Version 1.0
- Operational in both Active and Secondary Controller Modes
- Caliptra subsystem uses only target/secondary controller mode
- OCP Recovery Support

### 3. Life Cycle Controller (LCC)
- Spec-documented LC states and transitions
- Multiple test unlock tokens for supply chain protection
- Physical presence detection capability for RMA

### 4. Fuse Controller (FC)
- Caliptra core fuse map spec to Jan 10, 2025
- Production Debug Unlock Support
- Multi-test unlock token support
- Manufacturing time generic secret fuses for SoC usage

### 5. Manufacturer Control Unit (MCU):
- A dedicated VeeR instance for SoC-specific firmware
- PmP & User Mode Enabled
  
### 6. Manufacturer Control Interface (MCI):
- Caliptra Subsystem Boot Sequencer
- MCU SRAM with ECC
- Caliptra SS Registers
- Caliptra SS RAS Support
- MCU Mailboxes
- Caliptra Core LCC State Translator
- SoC Manufacturing Debug Unlock Support
- SoC Production Debug Unlock Support
- MCU ROM Interface Module
  
### Basic validation flows completed for:
- Recovery flow over I3C
- DMA from Caliptra to/from MCI
- MCU interaction with all the blocks (I3C, Caliptra, LCC, FC, MCU ROM, and MCI)
- Life Cycle Controller interactions and life cycle state changes
- Life Cycle Controller & Fuse Controller interactions

### Known Items
- Toolset for adding Generic SoC fuses & Generic IFP Secret fuses for SoC usage
- Regen FC for 1/16/2025 Caliptra core spec update
- I3C high frequency domain configuration parameters testing work in progress 
- Adams bridge memory ports
- Lint fixes
