# **Release Notes** #

## Caliptra Subsystem pre-2.2 Release Notes (Draft)
_*Status: Draft; not a final 2.2 release.*_

USB streaming boot support, security hardening, and integration spec updates since 2.1.

### 1. Caliptra Core
- VeeR dual-core lockstep (DCLS), memory address-integrity checks, and DCCM write-readback
- Shared masked HMAC-SHA-384/512 engine with updated seed and command interface (area/latency optimization)
- Key Vault boot-policy enforcement, key-length checks, and zeroization fixes; AES key masking enhancements
- Hardware ICCM SHA-384 measurement
- Explicit ECC/ML-DSA verification status
- Dual-iTRNG entropy combiner
- DMA command limit increased to 2 GiB, with route-specific limits; response-tracking, mailbox ECC, and AXI access fixes
- Adams Bridge architectural/Keccak masking, local storage/pipeline optimizations, and KV/zeroization fixes

### 2. I3C
- Updated I3C to v1p6 with recovery FIFO/PEC, CCC, IBI, and reset/error-handling improvements
- AXI interface updates; existing I3C and AXI streaming boot paths retained

### 3. Life Cycle Controller (LCC)
- Exposed lifecycle state validity, volatile RAW-unlock success, and escalation/check interfaces
- Clarified token provisioning and scan exclusions

### 4. Fuse Controller (FC)
- Hardened debug-intent handling, secret digest access, and UDS/Field Entropy programming restrictions
- Sticky PK-hash/ratchet-seed locks and lifecycle-qualified fuse-wrapper DFT enable
- Debug-unlock state fixes and multibit debug-lock controls

### 5. Manufacturer Control Interface (MCI)
- Hamming-coded boot FSM error detection
- Default-enabled Caliptra Core DCLS detection control and configuration locking
- Exclusive MCU mailbox SRAM ownership for image staging
- Optional MCU ROM patch SRAM: loaded by MCU ROM in TEST/DEV lifecycle states before Caliptra core boots; a loaded patch zeroizes the UDS/Field Entropy delivered to Caliptra; released to SoC as data memory when unused.

### 6. USB and MCU Peripherals
- USB 2.0 virtual hub with two downstream devices: MCU-owned DEV0 and SoC-owned DEV1
- DEV0 OCP Recovery over EP0 with an Indirect FIFO consumed by Caliptra over AXI
- USB recovery selection, interrupts, packet-memory interfaces, and AXI USER filtering

### Integration spec updates
- Named integration/trademark requirements and exemption-request guidance
- Clarified AXI USER isolation, USB access rules, clock/reset timing, CDC/RDC, and memory/fuse integration

### Validation updates
- Added USB hub/device/recovery/access-control, entropy, and boot-FSM tests
- Expanded crypto, I3C, fuse/lifecycle, and mailbox checks; fixed false-pass and reset/error handling
- Updated models, coverage, build flows, and register-generation checks

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

# Previous Releases #

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
