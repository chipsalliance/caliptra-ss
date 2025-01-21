# Caliptra Subsystem 0.8 Release Notes

## 1. Caliptra Core
- **Adams Bridge**
- **PQC Key Vault & Derivation Support**
- **OCP Recovery Support**
- Updated VeeR core pointing to VeeR 2.0 release
- Increased ROM, ICCM/DCCM, and Mailbox sizes for Caliptra 2.0
- Manufacturing Debug Unlock Support
- Production Debug Unlock Support
- All bug fixes since Caliptra core freeze

## 2. I3C
- Compliant with:
  - MIPI Alliance Specification for I3C Basic, Version 1.1.1
  - MIPI Alliance Specification for I3C HCI, Version 1.2
  - MIPI Alliance Specification for I3C TCRI, Version 1.0
- Operational in both Active and Secondary Controller Modes
- Caliptra subsystem uses only target/secondary controller mode
- OCP Recovery Support

## 3. Life Cycle Controller (LCC)
- Spec-documented LC states and transitions
- Multiple test unlock tokens for supply chain protection
- Physical presence detection capability for RMA

## 4. Fuse Controller (FC)
- Caliptra core fuse map spec to 10/1
- Production Debug Unlock Support
- Multi-test unlock token support
- Manufacturing time generic secret fuses for SoC usage

## 5. Manufacturer Control Unit (MCU)**:
  - A dedicated VeeR instance for SoC-specific firmware
  - PmP & User Mode Enabled

## 6. Manufacturer Control Interface (MCI)**:
  - Caliptra Subsystem Boot Sequencer
  - MCU SRAM with ECC
  - Caliptra SS Registers
  - Caliptra SS RAS Support
  - MCU Mailboxes
  - Caliptra Core LCC State Translator
  - SoC Manufacturing Debug Unlock Support
  - SoC Production Debug Unlock Support
  - MCU ROM Interface Module

## Basic validation flows completed for:
  - Recovery flow over I3C
  - DMA from Caliptra to/from MCI
  - MCU interaction with all the blocks (I3C, Caliptra, LCC, FC, MCU ROM, and MCI)
  - Life Cycle Controller interactions and life cycle state changes
  - Life Cycle Controller & Fuse Controller interactions

## Known Items
- Toolset for adding Generic SoC fuses & Generic IFP Secret fuses for SoC usage
- Regen FC for 1/16/2025 Caliptra core spec update
- I3C high frequency domain configuration parameters testing work in progress 
- Adams bridge memory ports
- Lint fixes