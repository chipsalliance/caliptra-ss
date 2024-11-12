![OCP Logo](./images/OCP_logo.png)

<p style="text-align: center;">Caliptra Subsystem Hardware Specification</p>

<p style="text-align: center;">Version 0.5</p>

<div style="page-break-after: always"></div>

# Scope

This document defines technical specifications for a subsystem design utilizing Caliptra RoT in Subystem Mode. This document, along with [Caliptra Hardware Specification](https://github.com/chipsalliance/caliptra-rtl/blob/main/docs/CaliptraHardwareSpecification.md), shall comprise the Caliptra Subsystem technical specification.


# Caliptra Subsystem Requirements
## Definitions
* RA: Recovery Agent
* MCI: Manufacturer Control Interface
* MCU: Manufacturer Control Unit
  
## Caliptra-Passive-Mode (Legacy)
SOC manages boot media peripherals and Caliptra is used as Root of trust for measurements.

## Caliptra-subsystem-mode 
Caliptra owns the recovery interface (peripheral independent) and Caliptra is THE RoT of the SoC. Any SOC specific variables that needs to be stored and retrieved securely from NV storage is handled using Caliptra.

## Caliptra Subsystem Architectural Requirements

1. MCU [Manufacturer Control Unit] runs Manufacturer specific FW authenticated, measured & loaded by Caliptra at boot time.
2. MCU will use Caliptra RT FW to auth/measure/load all of the FW belonging to the SOC.
3. MCU ROM/FW on MCU should be capable of performing SOC specific initialization.
4. MCU ROM/FW should be able to perform SoC management functions including performing reset control, SoC specific security policy enforcement, SOC initial configuration (eg. any GPIO programming, glitch detection circuits, reading/moving non-secret fuses etc.).
  * Note: Widgets that toggle the reset or other wires that set security permissions are SOC specific implementations.
6. Fuse controller for provisioning Caliptra fuses -> IFP (In-field programmable) fusing is performed by MCU RT; SW partition fuses in fuse controller are managed by MCU (ROM or RT); Caliptra HW is responsible for reading the secret fuses (Caliptra ROM, MCU ROM or any other SOC ROM or any RT FW should NOT have access to read the secret fuses in production).
7. Recovery stack must be implemented. Please refer to I3C recovery section for more details and references.
OCP Recovery registers implemented in I3C must follow the security filtering requirements specified in the recovery implementation spec (eg. MCU can ONLY access subset of the recovery registers as defined by the recovery implementation).
8. Supports silicon t0 boot to load and run required FW across chiplets.
9. OCP recovery stack is implemented in Caliptra for Caliptra-subsystem-mode
10. MCU SRAM (or part of the SRAM that is mapped for Code/Data execution) should be readable/writeable ONLY by Caliptra until Caliptra gives permission to MCU to use it.
11. Caliptra can only load its FW, SOC manifest and MCU FW by reading the recovery interface registers.
12. Caliptra ROM should know the offset of the recovery interface at its boot time. SOC has a choice to program this interface using MCU ROM or Hard strapped register address at integration time (Hard strapping at SOC integration time is recommended)
13. Caliptra HW must know the offset of the registers where secrets (UDS, FE) and assets (PK hashes) exist at boot time. These should be hard strapped/configured at integration time.
14. Caliptra ROM must know the address to where UDS-seed needs to be written to; this address should be hard strapped/configured at integration time.
15. Any registers holding secrets/assets in fuse controller must follow the same rules as Caliptra 1.0/2.0 fuse register requirements (eg. clear on debug, clear on read once etc.)
16. MCU SRAM and ROM sizes should be configurable at SOC integration time.

## Caliptra Subsystem HW Requirements

### Caliptra 2.0 HW requirements (Subsystem Support)
1. Full AXI read/write channels (aka AXI manager) for subsystem (for MCU and Caliptra)
    a. For backward compatibility, AXI mgr. interface can be a no-connect and that configuration is validated.
2. HW logic/Programmable DMA
  * Read MMIO space for variable length.
  * Data returned from the above read can be exposed directly to the FW OR allow it to be written to a subsystem/SOC destination as programmed by ROM/FW.
  * Programmable logic to allow for SOC directed writes (from FW or from the above route back) to be sent through the SHA accelerator.
  * (Future open/stretch goal): If AES engine accelerator is integrated into Caliptra, then implement decryption before sending the writes back to the destination programmed by the ROM/FW.
  * This widget should have accessibility in manufacturing and debug mode over JTAG (can be exposed using the same JTAG interface as Caliptra 1.0). Ensure through validation that no asset can be read using this widget in those modes.
3. Expand manuf flow register to include UDS programming request steps
4. SOC Key Release HW (Required for OCP Lock flow too)
  * Separate SOC Key Vault must be implemented (it is a separate structure from the current Caliptra KV).
  * In at least one configuration, the SOC KV must be implemented as an SRAM that is external and configurable by the SOC OR or an internal configurable SOC KV structure. If this is achievable within the Caliptra 2.0 milestone, only one of these would be the chosen implementation and configuration. This will be a design decision based on effort & schedule.
  * If implemented as a SRAM, data written and read into the SOC KV SRAM is decrypted & encrypted so that SOC DFT or other side channels cannot exfilterate the data.
  * Caliptra FW will indicate to the SOC KV Release HW to release the key by supplying the key handle to read from.
  * Destination address to which the key must be written to is programmed by the Caliptra FW into AXI MGR DMA HW.
  * SOC KV must have the same attributes as Caliptra internal KV. Additionally, it must also have an attribute of read-once and clear.

### Caliptra 2.0 HW requirements (Not subsystem related)
1. Ability to use two or more cryptos concurrently
2. Change APB -> AXI-Sub with the same capabilities (AXI USERID filtering replaces PAUSER based filtering, multiple targets for SHA acc, mailbox, fuses, registers etc. all)
3. Future/Stretch Goal: Parity support on AXI-SUB & MGR


### MCU HW requirements
1. MCU should not be in the FIPS boundary and must not have any crypto functions. MCU must use Caliptra for any security flows (eg. security policy authorization) or traditional RoT support (eg. SPDM).
2. MCU VeeR must support PMP & User mode.
3. MCU AXI is directly connected to the SOC fabric in a way that allows a MMIO based control of the SoC as required for SOC security, manageability and boot functionality.
4. MCU HW should add AXI-ID without any involvement of the ROM or FW running on the MCU; Implying any AXI access out of MCU (LSU side) should carry MCU USERID that HW populates.
5. MCU executes from a SRAM that is at subsystem level.
6. MCU uses instruction cache for speed up
7. It is required that all NV read/writes (eg. NV variables in flash) that require a RoT support to securely store/restore must go through Caliptra.
8. NV-storage peripheral shall be built in such a way that it will only accept transactions from MCU.
9. Support for MCU first fetch vector to direct towards MCU SRAM post reset 


### Subsystem Components HW requirements
#### Fabric
1. AXI Interconnect connects Caliptra, I3C, Fuse Controller, Life Cycle Controller, MCU and its memory components with the rest of the SOC.
  * **Note:** Because each SOC integration model is different, AXI interconnect is NOT implemented by the subsystem but subsystem must validate using an AXI interconnect VIP to ensure all the components operate per the flows documented in this specification.
  * For the VIP interconnect configuration, all subtractively decoded transactions are sent towards SoC. AXI interconnect & Subsystem is validated with the assumption that all of them are running on the same clock domain.
2. To be documented: AXI-USERID requirements

#### MCU SRAM 
1. Since it's used for instruction and data execution – therefore requires AXI Sub with USERID filtering.
2. Provide JTAG accessibility to allow for SRAM to be populated in a secured debug mode at power on time (debug policies will be same as Caliptra)
3. MCU SRAM should have an aperture that can only be unlocked by Caliptra after it loads the image
4. MCU SRAM has an aperture for MCU ROM to use part of the SRAM as a stack for its execution.
5. MCU SRAM supports an aperture to be used as a MCU Mailbox.

#### MCU ROM
* MCU ROM also needs to have AXI Sub for any data access from MCU and thereby requires AXI-ID/USERID filtering.

#### I3C 
1. I3C on AXI interconnect with AXI Subordinate
2. Spec 1.1.1 aligned, but only with optional features that are required per PCIe ECN # <>
3. AXI Sub must be supported.
4. UserID to MCU and Caliptra
5. MCU access lock for I3C recovery and data (FIFO) registers until recovery flow is completed. In other words, MCU ROM must not impact the data flow into Recovery IFC registers.
Stretch Goal: DMA data payload back to destination (Caliptra or MCU) 

#### Fuse Controller
1. AXI sub interface
2. Secrets (separate USERID and access constraints) vs SW partition separation
3. Registers implemented for “Secrets” should follow the same rules as Caliptra (no scan, clear on specific life cycle/security states)
4. Life cycle transition shall be implemented in hardware with no ROM/FW implementation and provides redundancy against fault & glitch attacks in the digital logic itself.
5. SOC debug in production mode shall be supported with the help Caliptra through post quantum resilient algorithms.
6. When debug mode is intended to be enabled & when enabled, all secrets/assets as defined should be wiped and provide the indication to SOC for any secrets/assets it may have.

#### MCI
* HW logic to move secret fuses from Fuse controller to Caliptra.

## Caliptra Subsystem Hardware Block Diagram

*Figure 1: Caliptra Subsystem Block Diagram*

![](https://github.com/chipsalliance/Caliptra/blob/main/doc/images/Subsystem.png)


# Caliptra Subsystem Architectural Flows
Please refer to [Caliptra Security Subsystem Specification](https://github.com/chipsalliance/Caliptra/blob/main/doc/Caliptra.md#caliptra-security-subsystem)), for more details

# I3C Recovery Interface
The I3C recovery interface acts as a standalone I3C target device for recovery. It will have a unique address compared to any other I3C endpoint for the device. It will comply with I3C Basic v1.1.1 specification. It will support I3C read and write transfer operations. It must support Max read and write data transfer of 1-256B excluding the command code (1 Byte), length (2 Byte), and PEC (1 Byte), total 4 Byte I3C header. Therefore, max recovery data per transfer will be limited to 256-byte data.
	
I3C recovery interface is responsible for the following list of actions: 
1. Responding to command sent by Recovery Agent (RA)
2. Updating status registers based on interaction of AC-RoT and other devices
3. Asserting / Deasserting “payload_available” & “image_activated” signals

## Recovery Interface hard coded logic
Hardware registers size is fixed to multiple of 4 bytes, so that firmware can read or write with word boundary. Address offset will be programmed outside of the I3C device. Register access size must be restricted to individual register space and burst access with higher size must not be allowed.

**TODO:** Add a link to the picture

## Hardware Registers
Hardware registers size is fixed to multiple of 4 bytes, so that firmware can read or write with word boundary. Address offset will be programmed outside of the I3C device. Register access size must be restricted to individual register space and burst access with higher size must not be allowed.

**Note:** Accessing the same address for INDIRECT_FIFO_DATA register will write or read the FIFO. It will not be available to access randomly as specified by the specification. 

**TODO:** Add a link to rdl

## Recovery Interface Wires
	
1. **Payload available**
  * The Recovery Interface (I3C target) should receive a write transaction to INDIRECT_FIFO_DATA reg from BMC - 256B + 4B (Header), and wait for each I3C write to finish. Once I3C write transaction to INDIRECT_FIFO_DATA register is completed and PEC verification is successful, then the I3C target must assert "payload_available". DMA assist must wait for "payload_available" before reading. It must read 256B or last read with remaining data.
  * The "payload_available" signal remains asserted until Recovery Interface receives Read from DMA over AXI for INDIRECT_FIFO_DATA.
2. **Image_activated**
  * The I3C target will assert "image_activated" signal as soon as write to RECOVERY_CTRL register is received.
  * ROM will clear “image_activated” bit by writing to RECOVERY_CTRL register via DMA assist after the image is authenticated. As defined in the OCP Recovery Specification, RECOVERY_CTRL, byte 2 is used to specify the image activation control, and is Write-1-Clear. ROM must write 0xFF to this field to clear the image recovery status, which will also result in the Recovery Interface deasserting the “image_activated” signal to Caliptra.

## RT firmware requirements
Firmware must program DMA assist with correct image size (multiple of 4B) + FIXED Read + block size is 256B (burst / FIFO size). Firmware must wait for "image_activated" signal to assert before processing the image. Once the image is processed, firmware must initiate a write with data 1 via DMA to clear byte 2 “Image_activated” of the RECOVERY_CTRL register. This will allow BMC to initiate subsequent image writes. 

## I3C and Caliptra-AXI Interactions
Received transfer data can be obtained by the driver via a read from XFER_DATA_PORT register. Received data threshold is indicated to BMC by the controller with TX_THLD_STAT interrupt if RX_THLD_STAT_EN is set. The RX threshold can be set via RX_BUF_THLD. In case of a read when no RX data is available, the controller shall raise an error on the frontend bus interface (AHB / AXI).

# Caliptra AXI Manager & DMA assist

# Caliptra Fuse Controller

# Caliptra Life Cycle Controller

# Manufacturer Control Unit (MCU)

# Manufacturer Control Interface (MCI)

# Subsystem Memory Map

# Subsystem HW Security
