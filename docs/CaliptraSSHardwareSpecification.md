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

*Figure: Caliptra Subsystem Block Diagram*

![](https://github.com/chipsalliance/Caliptra/blob/main/doc/images/Subsystem.png)


# Caliptra Subsystem Architectural Flows
Please refer to [Caliptra Security Subsystem Specification](https://github.com/chipsalliance/Caliptra/blob/main/doc/Caliptra.md#caliptra-security-subsystem)), for more details

# I3C Streaming Boot (Recovery) Interface
The I3C recovery interface acts as a standalone I3C target device for recovery. It will have a unique address compared to any other I3C endpoint for the device. It will comply with I3C Basic v1.1.1 specification. It will support I3C read and write transfer operations. It must support Max read and write data transfer of 1-256B excluding the command code (1 Byte), length (2 Byte), and PEC (1 Byte), total 4 Byte I3C header. Therefore, max recovery data per transfer will be limited to 256-byte data.
	
I3C recovery interface is responsible for the following list of actions: 
1. Responding to command sent by Recovery Agent (RA)
2. Updating status registers based on interaction of AC-RoT and other devices
3. Asserting / Deasserting “payload_available” & “image_activated” signals

## Streaming Boot (Recovery) Interface hard coded logic
Hardware registers size is fixed to multiple of 4 bytes, so that firmware can read or write with word boundary. Address offset will be programmed outside of the I3C device. Register access size must be restricted to individual register space and burst access with higher size must not be allowed.

*Figure: I3C Streaming Boot (Recovery) Interface Logic Block Diagram*

![](https://github.com/chipsalliance/caliptra-ss/blob/bpillilli-main-spec-md-update/docs/images/I3C-Recovery-IFC.png)

## Hardware Registers
Hardware registers size is fixed to multiple of 4 bytes, so that firmware can read or write with word boundary. Address offset will be programmed outside of the I3C device. Register access size must be restricted to individual register space and burst access with higher size must not be allowed.

**Note:** Accessing the same address for INDIRECT_FIFO_DATA register will write or read the FIFO. It will not be available to access randomly as specified by the specification. 

**TODO:** Add a link to rdl -> html file

## Streaming Boot (Recovery) Interface Wires
	
1. **Payload available**
  * The Recovery Interface (I3C target) should receive a write transaction to INDIRECT_FIFO_DATA reg from BMC - 256B + 4B (Header), and wait for each I3C write to finish. Once I3C write transaction to INDIRECT_FIFO_DATA register is completed and PEC verification is successful, then the I3C target must assert "payload_available". DMA assist must wait for "payload_available" before reading. It must read 256B or last read with remaining data.
  * The "payload_available" signal remains asserted until Recovery Interface receives Read from DMA over AXI for INDIRECT_FIFO_DATA.
2. **Image_activated**
  * The I3C target will assert "image_activated" signal as soon as write to RECOVERY_CTRL register is received.
  * ROM will clear “image_activated” bit by writing to RECOVERY_CTRL register via DMA assist after the image is authenticated. As defined in the OCP Recovery Specification, RECOVERY_CTRL, byte 2 is used to specify the image activation control, and is Write-1-Clear. ROM must write 0xFF to this field to clear the image recovery status, which will also result in the Recovery Interface deasserting the “image_activated” signal to Caliptra.

## I3C Streaming Boot (Recovery) Flow

Please refer to [Caliptra Security Subsystem Recovery Sequence](https://github.com/chipsalliance/Caliptra/blob/main/doc/Caliptra.md#caliptra-subsystem-recovery-sequence).

*Figure: Caliptra Subsystem I3C Streaming Boot (Recovery) Flow*
![](https://github.com/chipsalliance/caliptra-ss/blob/bpillilli-main-spec-md-update/docs/images/CSS-Recovery-Flow.png)

## Caliptra ROM Requirements
Caliptra ROM & RT firmware must program DMA assist with correct image size (multiple of 4B) + FIXED Read + block size is 256B (burst / FIFO size). Caliptra ROM & RT Firmware must wait for "image_activated" signal to assert before processing the image. Once the image is processed, Caliptra ROM & RT firmware must initiate a write with data 1 via DMA to clear byte 2 “Image_activated” of the RECOVERY_CTRL register. This will allow BMC (or streaming boot initiator) to initiate subsequent image writes. 

## I3C and Caliptra-AXI Interactions
Received transfer data can be obtained by the driver via a read from XFER_DATA_PORT register. Received data threshold is indicated to BMC by the controller with TX_THLD_STAT interrupt if RX_THLD_STAT_EN is set. The RX threshold can be set via RX_BUF_THLD. In case of a read when no RX data is available, the controller shall raise an error on the frontend bus interface (AHB / AXI).

# Caliptra AXI Manager & DMA assist

# Caliptra SS Fuse Controller

# Caliptra SS Life Cycle Controller
It is an overview of the architecture of the Life-Cycle Controller (LCC) Module for its use in the Caliptra Subsystem. The LCC is responsible for managing the life-cycle states of the system, ensuring secure transitions between states, and enforcing security policies.

## Caliptra Subsystem, SOC Debug Architecture Interaction
Figure below shows the Debug Architecture of the Caliptra Subsystem and some important high-level signals routed towards SOC. The table in Key Components and Interfaces section shows all the signals that are available to SOC (outside of Caliptra Subsystem usage).

*Figure: Caliptra Subsystem & SOC Debug Architecture Interaction*
![](https://github.com/chipsalliance/caliptra-ss/blob/bpillilli-main-spec-md-update/docs/images/LCC-SOC-View.png)
**Note:** SoC Debug Architecture of the Caliptra Subsystem with LCC; the red dashed circles highlight the newly added blocks and signals.

The figure below shows the LCC state transition and Caliptra Subsystem enhancement on LCC state transitions. It illustrates the life cycle flow of Caliptra Subsystem.

*Figure: Caliptra Subsystem Life Cycle Controller Summary*
![](https://github.com/chipsalliance/caliptra-ss/blob/bpillilli-main-spec-md-update/docs/images/LCC-Summary.png)

**Note:** Caliptra Subsystem life cycle flow. This flow shows legal state transitions in life cycle controller by excluding its invalid states for simplicity.

## Caliptra Subsystem LCC State Definitions

| **Name** 	| **Encoding** 	| **Description** |
| :--------- 	| :--------- 	| :--------- 	 |
| RAW | OTP | This is the default state of the OTP. During this state, no functions other than transition to TEST_UNLOCKED0 are available. The token authorizing the transition from RAW to TEST_UNLOCKED0 is a value that is secret global to all devices. This is known as the RAW_UNLOCK token. |
| TEST_LOCKED{N} | OTP | TEST_LOCKED{N} states have identical functionality to RAW state and serve as a way for the Silicon Creator to protect devices in transit. It is not possible to provision OTP root secrets during this state. This is enforced by hardware and is implementation defined. To progress from a TEST_LOCKED state to another TEST_UNLOCKED state, a TEST_UNLOCK token is required.|
| TEST_UNLOCKED{N} | OTP | Transition from RAW state using OTP write. This state is used for manufacturing and production testing. During this state: uCTAPs (microcontroller TAPs) are enabled; Debug functions are enabled; DFT functions are enabled. **Note:** during this state it is not possible to provision specific OTP root secrets. This will be enforced by hardware. It is expected that during TEST_UNLOCKED0 the TEST_UNLOCK and TEST_EXIT tokens will be provisioned into OTP. Once provisioned, these tokens are no longer readable by software.|
| PROD | OTP | Transition from TEST_UNLOCKED or TEST_LOCKED state via OTP writes. PROD is a mutually exclusive state to MANUF and PROD_END. To enter this state, a TEST_EXIT token is required. This state is used both for provisioning and mission mode. During this state: uCTAPs (microcontroller TAPs) are disabled; Debug functions are disabled; DFT functions are disabled; Caliptra Subsytem can grant SoC debug unlock flow if the conditions provided in “SoC Debug Flow and Architecture for Production Mode” section are satisfied. SoC debug unlock overwrites the signals and gives the following cases: uCTAPs (microcontroller TAPs) are enabled; Debug functions are enabled based on the defined debug policy; DFT functions are disabled |
| PROD_END | OTP | This state is identical in functionality to PROD, except the device is never allowed to transition to RMA state. To enter this state, a TEST_EXIT token is required.|
| MANUF | OTP | Transition from TEST_UNLOCKED state via OTP writes. This is a mutually exclusive state to PROD and PROD_END. To enter this state, a TEST_EXIT token is required. This state is used for developing provisioning and mission mode software. During this state: uCTAPs (microcontroller TAPs) are enabled conditionally (uCTAP Unlock Token Routine section); Debug functions are enabled; DFT functions are disabled |
| RMA | OTP | Transition from TEST_UNLOCKED / PROD / MANUF via OTP write. It is not possible to reach this state from PROD_END. When transitioning from PROD or MANUF, an RMA_UNLOCK token is required. When transitioning from TEST_UNLOCKED, no RMA_UNLOCK token is required. During this state: uCTAPs (microcontroller TAPs) are enabled; Debug functions are enabled; DFT functions are enabled |
| SCRAP | OTP | Transition from any manufacturing state via OTP write. During SCRAP state the device is completely dead. All functions, including CPU execution are disabled. The only exception is the TAP of the life cycle controller which is always accessible so that the device state can be read out. No owner consent is required to transition to SCRAP. Note also, SCRAP is meant as an EOL manufacturing state. Transition to this state is always purposeful and persistent, it is NOT part of the device’s native security countermeasure to transition to this state. |
| INVALID | OTP | Invalid is any combination of OTP values that do not fall in the categories above. It is the “default” state of life cycle when no other conditions match. Functionally, INVALID is identical to SCRAP in that no functions are allowed and no transitions are allowed. A user is not able to explicitly transition into INVALID (unlike SCRAP), instead, INVALID is meant to cover in-field corruptions, failures or active attacks.|

## DFT & DFD LC States

In addition to the decoding signals of the Life-Cycle Controller (LCC) proposed in the OpenTitan open-source silicon Root of Trust (RoT) project, we introduce a new signal: Caliptra_SS_uCTAP_HW_DEBUG_EN  and renamed HW_DEBUG_EN  as SOC_HW_DEBUG_EN. These signals are critical for managing the test and debug interfaces within the Caliptra Subsystem, as well as at the broader SoC level.

While this architecture document explains how the Caliptra Subsystem provides DFT and DFD mechanisms through the DFT_EN, SOC_HW_DEBUG_EN, and Caliptra_SS_uCTAP_HW_DEBUG_EN signals, it also offers greater flexibility by supporting various SoC debugging options through the broader SoC debug infrastructure. The architecture does not constrain the SoC’s flexibility with the core security states of Caliptra and LCC states.
We establish a set of clear guidelines for how the Caliptra Subsystem transitions through the unprovisioned, manufacturing, and production phases, ensuring security. However, this architecture remains flexible, offering multiple levels of debugging options in production debug mode. Level 0 is designated for debugging the Caliptra Subsystem itself, while higher levels can be interpreted and customized by the SoC designer to implement additional debugging features. For instance, if the SoC designer wishes to include extra DFT and DFD capabilities, they can utilize one of the debug levels provided during production debug mode and expand its functionality accordingly. For more details, see “SoC Debug Flow and Architecture for Production Mode” Section and “Masking Logic for Debugging Features in Production Debug Mode” Section.

The DFT_EN signal is designed to] control the scan capabilities of both the Caliptra Subsystem and the SoC. When DFT_EN is set to HIGH, it enables the scan chains and other Design for Testability (DFT) features across the system, allowing for thorough testing of the chip. This signal is already provided by the existing LCC module, ensuring compatibility with current test structures. However, the SoC integrator has the flexibility to assign additional functionality to one of the debugging options provided by the debug level signals during production debug mode. For example, at the SoC level, an integrator may choose to use one of these levels to enable broader SoC DFT features, allowing for system-level testing while maintaining Caliptra's protection. Additionally, SoC can override DFT_EN and set it to HIGH by using the infrastructure defined in “Masking Logic for Debugging Features in Production Debug Mode” Section.

The SOC_HW_DEBUG_EN signal is a new addition that governs the availability of the Chip-level TAP (CLTAP). CLTAP provides a hardware debug interface at the SoC level, and it is accessible when SOC_HW_DEBUG_EN is set to HIGH. For further details on how this signal integrates with the overall system, refer to the “TAP Pin Muxing” Section of this document.

In the manufacturing phase, the Caliptra Subsystem asserts SOC_HW_DEBUG_EN high, with the signal being controlled by the LCC. In PROD mode, this signal is low. However, the SoC integrator has the flexibility to enable CLTAP during production debug mode by incorporating additional logic, such as an OR gate, to override the SOC_HW_DEBUG_EN signal, like DFT_EN. This architecture provides a mask register that allows SoC to program/configure this overriding mechanism at integration time or using MCU ROM. This allows the SoC to maintain control over hardware debug access while preserving the intended security protections in production.

Finally, the Caliptra_SS_uCTAP_HW_DEBUG_EN signal is introduced to manage the microcontroller TAPs (uCTAPs) within the Caliptra subsystem. Although DFT_EN and SOC_HW_DEBUG_EN are directly controlled by LCC, Caliptra_SS_uCTAP_HW_DEBUG_EN is controlled by two conditions set by LCC and Caliptra. This document provides more details about these two conditions in uCTAP Unlock Token Routine. These TAPs are open before the development phase has been entered; and after that will be accessible during the LCC’s MANUF and PROD states, only if the token authentication is successful. The following table shows DFT_EN, SOC_HW_DEBUG_EN, and Caliptra_SS_uCTAP_HW_DEBUG_EN positions based on the LCC’s states. 

*Table: LCC State and State Decoder output ports*
| **LCC State\Decoder Output** 	| **DFT_EN** 	| **SOC_HW_DEBUG_EN** 	| **Caliptra_SS_uCTAP_HW_DEBUG_EN** |
| :--------- 			| :--------- 	| :--------- 	 	| :--------- 	 |
| RAW 				| Low 		| Low 			| Low |
| TEST_LOCKED 			| Low 		| Low 			| Low |
| TEST_UNLOCKED 		| High 		| High 			| High |
| MANUF* 			| Low 		| High 			| TOKEN - CONDITIONED** |
| PROD* 			| TOKEN - CONDITIONED** | TOKEN - CONDITIONED** | TOKEN - CONDITIONED** |
| PROD_END 			| Low 		| Low 			| Low | 
| RMA 				| High 		| High 			| High | 
| SCRAP 			| Low 		| Low 			| Low |
| INVALID 			| Low 		| Low 			| Low |
| POST_TRANSITION 		| Low 		| Low 			| Low |



*: Caliptra can enter debug mode and update these signals even though LCC is in MANUF or PROD states. This case is explained in “How does Caliptra enable uCTAP_UNLOCK?” and “SoC Debug Flow and Architecture for Production Mode”.

**: Caliptra_SS_uCTAP_HW_DEBUG_EN can be high if Caliptra SS grants debug mode (either manufacturing or production). This case is explained in “How does Caliptra enable uCTAP_UNLOCK?” and “SoC Debug Flow and Architecture for Production Mode”. SOC_HW_DEBUG_EN and DEF_EN can be also set high to open CLTAP and enable DFT by SoC design support. However, this condition also needs to go through the flow described in “SoC Debug Flow and Architecture for Production Mode”. Caliptra Subsystem state should be set to either the manufacturing mode debug unlock or Level 0 of the production debug unlock to enable access to the Caliptra and MCU uCTAPs.

## TAP Pin Muxing
The LCC includes a TAP interface, which operates on its own dedicated clock and is used for injecting tokens into the LCC. Notably, the LCC TAP interface remains accessible in all life cycle states, providing a consistent entry point for test and debug operations. This TAP interface can be driven by either the TAP GPIO pins or internal chip-level wires, depending on the system's current configuration.

*Figure: Caliptra Subsystem Life Cycle Controller Summary*
![](https://github.com/chipsalliance/caliptra-ss/blob/bpillilli-main-spec-md-update/docs/images/TAP-Pin-Muxing.png)
**Note:** Above figure of TAP pin muxing block diagram with a conceptual representation. SOCs may implement this in their own way

SOC logic incorporates the TAP pin muxing to provide the integration support and manage the connection between the TAP GPIO pins and the Chip-Level TAP (CLTAP). As illustrated in figure above, this muxing logic determines the source that drives the LCC TAP interface. The selection between these two sources is controlled by the SOC_HW_DEBUG_EN signal. When SOC_HW_DEBUG_EN is set to high, control is handed over to the CLTAP, allowing for chip-level debug access through the TAP GPIO pins. Conversely, when SOC_HW_DEBUG_EN is low, the TAP GPIO pins take control, enabling external access to the LCC TAP interface.

**_LCC State and State Decoder Output Ports Table_** (**TODO:** Add link) outlines the specific LCC states that enable the SOC_HW_DEBUG_EN signal. These states include TEST_UNLOCK, MANUF, PRDO, and RMA. In these states, the LCC allows internal chip-level debug access via CLTAP, thereby facilitating advanced debugging capabilities. This muxing approach ensures that the TAP interface is appropriately secured, and that access is granted only under specific conditions, aligning with the overall security and functional requirements of the Caliptra Subsystem.

TAP pin muxing also enables routing to Caliptra TAP. This selection happens when DEBUG_INTENT_STRAP is high. This selection is done through the GPIO and indicates that Caliptra will enter debug mode if the secret tokens are provided. Caliptra Subsystem has two debug modes: manufacturing debug and production debug. Entering these debug flows are explained in the following sections: 
	* **“How does Caliptra enable uCTAP_UNLOCK?”** *TODO:** Add links
	* **“SoC Debug Flow and Architecture for Production Mode” and “Masking Logic for Debugging Features in Production Debug Mode”**. **TODO:** Add links
  
**Note:** The Caliptra TAP can run exact flow with AXI, targeting the mailbox and SOC provides that interface to platform.

## Manufacturing Debug Unlock Hardware Logic

The figure below illustrates the logic used to control the Caliptra_SS_uCTAP_HW_DEBUG_EN signal, which is a critical part of enabling the microcontroller TAP (uCTAP) debugging interface in the Caliptra Subsystem. This diagram shows an illustration of how uCTAP opens. However, the functionality of this logic will be implemented in MCI. The Caliptra_SS_uCTAP_HW_DEBUG_EN signal is governed by two primary inputs: SOC_HW_DEBUG_EN and a control signal driven by Caliptra. This signal opens uCTAP for MCU and Caliptra.

*Figure: Caliptra Subsystem Manuf Debug Unlock Hardware Logic*
![](https://github.com/chipsalliance/caliptra-ss/blob/bpillilli-main-spec-md-update/docs/images/Manuf-Debug-Unlock.png)
**Note:** This qualification logic is implemented within MCI block

To assert Caliptra_SS_uCTAP_HW_DEBUG_EN high, the SOC_HW_DEBUG_EN signal must always be high, except SOC production debug mode case (see “SoC Debug Flow and Architecture for Production Mode” Section). This ensures that the uCTAP interface is only enabled when the system is in a secure and authorized state. According to the figure, SOC_HW_DEBUG_EN is derived from the LCC states. Specifically, SOC_HW_DEBUG_EN is high when the LCC is in the TEST_UNLOCKED, MANUF, or RMA states. These are the only states where hardware debugging via the uCTAP interface is permitted. However, SOC_HW_DEBUG_EN can be set high by SoC during the production debug mode (see “Masking Logic for Debugging Features in Production Debug Mode”).

When the LCC is in the MANUF state, an additional condition is required for Caliptra_SS_uCTAP_HW_DEBUG_EN to be asserted high. In this case, Caliptra must actively enable the signal, which is indicated by the uCTAP_UNLOCK control line. This allows for controlled and conditional access to the uCTAP interface during the development phase, ensuring that debugging is only allowed when it is explicitly permitted by the system's security policies.

The AND gate in the figure symbolizes this logic, showing that Caliptra_SS_uCTAP_HW_DEBUG_EN can only be high if both SOC_HW_DEBUG_EN is high, and the specific conditions driven by Caliptra are met. This design ensures that the uCTAP interface is securely controlled, limiting access to authorized lifecycle states and further protected by additional checks during the development phase.

**Note:** This architecture provides an extension on LCC state with SoC production debug logic. This logic is configured to provide an additional layer to unlock debugging in the production phase. This logic can override Caliptra_SS_uCTAP_HW_DEBUG_EN and sets this signal high (see “SoC Debug Flow and Architecture for Production Mode” Section and “Masking Logic for Debugging Features in Production Debug Mode”).

### How does Caliptra enable uCTAP_UNLOCK for manufacturing debug mode?

The following figure illustrates how Caliptra Subsystem enters the manufacturing debug mode. To enter this mode, LCC should be in MANUF state. While being in manufacturing debug mode, LCC does not change its state from MANUF to any other state. During the MANUF state, Caliptra Subsystem can enable manufacturing debug flow by following steps:

*Figure: Caliptra Subsystem Manuf Debug Life Cycle View*
![](https://github.com/chipsalliance/caliptra-ss/blob/bpillilli-main-spec-md-update/docs/images/Manuf-Debug-LifeCycle.png)
**Note:** The flow diagram on the right side shows the LCC states (grey boxes) and their transitions, while the flow diagram on the left illustrates Caliptra SS’s enhancements to the LCC for the manufacturing phase. Specifically, the flow on the left depicts the routine for entering manufacturing debug mode.

#### Flow Explanation:

1. **(Platform) Assert BootFSMBrk :** Temporarily halting the Caliptra HW bootfsm boot process to allow for secure operations like token injection and verification.
2. **(Platform) Assert DEBUG_INTENT_STRAP:** If Caliptra core HW samples this pin as high and sees that LCC is in MANUF mode, it prepares itself for entering debug mode. Once the DEBUG_INTENT_STRAP is detected, Caliptra HW immediately wipes out its secret assets, including the Unique Device Secret (UDS) and Field entropy, ensuring that no sensitive data remains accessible. If this Pin is not high, Caliptra continues always in non-debug mode without taking any further action listed with the following states.
3. **(Platform over TAP)** MANUF_DEBUG_UNLOCK_REQ: The system intends to be in debug mode for manufacturing services.
4. **(Platform over TAP)** Write to Boot Continue: Resuming the boot process after halting it with BootFSMBrk.
5. **ROM reads MANUF_DEBUG_UNLOCK_REQ** at optimal time for ROM and clears mailbox lock
6. **Platform over TAP requests Caliptra mailbox lock**. If lock is obtained, then platform over TAP writes to TAP mailbox to inject Token via TAP Register Write: Enabling the injection of a token through TAP and writing to a specific register. The injected token is combined with a 256-bit nonce value that is updated for each boot session and generated by ROM. **TODO:** Update this step with the latest HW implementation
7. **ROM Executes Hash Hashing:** Calculates the authentication value of the injected token using a hash-core which is a cryptographic authentication technique that uses a hash function and a secret key. Before starting this operation, ROM also asserts MANUF_DEBUG_UNLOCK_IN_PROGRESS.
8. **Token Comparison:** A constant-time comparison between the authentication values of injected token and the FUSE content.
9. **ROM Drives MANUF_DEBUG_UNLOCK Signal:** The ROM writes to a register that controls the MANUF_DEBUG_UNLOCK signal based on the result of the token verification.

**Note:** The manufacturing debug flow relies on the hash comparison hardness rather than an authentication check provided with an asymmetric cryptography scheme. However, the following sections show that production debug flow relies on asymmetric cryptography scheme hardness. The reason behind this choice is that the manufacturing phase is the early phase of the delivery, and this phase is entered in an authorized entity’s facility. Therefore, this architecture keeps the manufacturing phase simpler.

The pseudo code given below explains the details of the token authentication.

**// Step 1: Assert BootFSMBrk to Caliptra and Debug intent strap GPIO pin**
Assert DEBUG_INTENT_STRAP  // Caliptra HW erases the secret assets and open Caliptra TAP.

Assert BootFSMBrk() // Caliptra HW is paused

**// Step 2: Request MANUF_DEBUG_UNLOCK_REQ service**
WriteToRegister(DEBUG_SERVICE_REQ_MANUF_DEBUG_UNLOCK, 1)  // TAP write to Caliptra HW

**// Step 3: Write to Boot Continue to proceed with the boot sequence**
WriteToRegister(BOOT_CONTINUE, 1)  // Caliptra ROM continues by GO command of TAP

**// Step 4: TAP reads waiting for Caliptra mailbox lock**
ReadRegister(CALIPTRA MAILBOX STS)

**// Step 5: TAP Write to Caliptra mailbox with payload & command**
MANUF_DEBUG_token_via_Caliptra_TAP = ReceiveTokenViaTAP() // Token injected through Caliptra TAP

**// Step 6: Caliptra ROM indicates that the authentication process is in progress**
if (LCC_state == MANUF) {
	WriteToRegister(MANUF_DEBUG_UNLOCK_IN_PROGRESS, 1)  // by Caliptra ROM
/*        	TOKEN FORMAT =  (64’h0 || 128-bit raw data || 64’h0)
The raw data is padded with 64-bit zeros by adding suffix and prefix by Caliptra ROM.
256-bit nonce is generated and concatenated with padded token  by Caliptra ROM.*/
WriteToRegister(SHA_512_API_Reg, (token || nonce_0)) // Store token in the pre-message register

**// Step 7: Caliptra ROM.performs hashing and token verification**
ROM_ExecAlgorithm() {
expected_token = SHA_512(SHA_512_API_Reg) // Hash-based token calculation by Caliptra ROM.
fuse_value = ReadFromFUSE() // Read secret value from FUSE by Caliptra ROM.
 // Hash-based token calculation   by Caliptra ROM.   
stored_token = SHA_512(64’h0 || fuse_value || 64’h0  || nonce_0) 
	if (expected_token == stored_token) {
	WriteToRegister(MANUF_DEBUG_UNLOCK_SUCCESS, 1)  // set by Caliptra ROM
	WriteToRegister(MANUF_DEBUG_UNLOCK_IN_PROGRESS, 0)  // set by Caliptra ROM
    	WriteToRegister(uCTAP_UNLOCK, 1) // If tokens do match, unlock uCTAP by Caliptra ROM
	} else {
	WriteToRegister(MANUF_DEBUG_UNLOCK_FAILURE, 1)  // set by Caliptra ROM
	WriteToRegister(MANUF_DEBUG_UNLOCK_IN_PROGRESS, 0)  // set by Caliptra ROM
    	WriteToRegister(uCTAP_UNLOCK, 0) // If tokens don't match, do not unlock uCTAP by Caliptra ROM
	}
 }
}

## Production Debug Unlock Architecture

The Caliptra Subsystem includes SoC debugger logic that supports Caliptra’s production debug mode. This debugger logic extends the capabilities of the Lifecycle Controller (LCC) by providing a production debug mode architecture that the LCC does not inherently support, except in the RMA state. This architecture manages the initiation and handling of the production debug mode separately from the LCC's lifecycle states.

The process of enabling production debug mode begins when the DEBUG_INTENT_STRAP pin is asserted high via the SoC’s GPIO. This pin signals Caliptra to start the debug mode when the LCC is in the PROD state. Even though the DEBUG_INTENT_STRAP can be set high at any time, Caliptra evaluates the request only during two distinct phases: Pre-ROM execution and Post-ROM execution.

In addition to DEBUG_INTENT_STRAP pin, there is also SoC-based DEBUG intent strap configuration, which has two values: DEBUG_AUTH_PK_HASH_REG_BANK_OFFSET and NUM_OF_ DEBUG_AUTH_PK_HASHES. The value DEBUG_AUTH_PK_HASH_REG_BANK_OFFSET represents an address offset, while NUM_OF_ DEBUG_AUTH_PK_HASHES defines how many registers are available for reading. These two values establish the debug policy depth, allowing flexibility beyond the earlier limit of N number public keys for different debugging levels. When the subsystem powers up, Caliptra hardware latches and locks the DEBUG_AUTH_PK_HASH_REG_BANK_OFFSET and NUM_OF_ DEBUG_AUTH_PK_HASHES values, ensuring that these cannot be modified later through firmware or any run-time activity. NUM_OF_ DEBUG_AUTH_PK_HASHES is needed to prevent out-of-bound access.

Once the DEBUG_INTENT_STRAP is detected, Caliptra immediately wipes out its secret assets, including the Unique Device Secret (UDS) and Field entropy, ensuring that no sensitive data remains accessible. After erasing the secret assets, Caliptra opens the TAP interface (in a safe mode to write to registers, not for active debug), which allows the debugger to interact with the system. The debugger verifies that the TAP interface is open by reading the TAP CSR (FIXME: to be documented once defined). The next step involves the debugger sending a Hybrid public key and a payload (employing both MLDSA and ECC cryptosystems) to Caliptra through the TAP interface. Caliptra receives these packages and writes them to its MailBox for further processing.

At this point, the debugger triggers the continuation of the boot sequence by setting the CPTRA_BOOTFSM_GO signal high through the TAP interface. This command signals Caliptra’s BootFSM to proceed. If the debug mode request occurs during run-time (after ROM execution), the debugger sets the GO command through the MailBox instead. Upon receiving the GO command, Caliptra locks the data in the MailBox to ensure its integrity, while the debugger waits for Caliptra to evaluate the request.

When a public key corresponding to a specific debug level is provided, denoted by the number i (Index_Of_Public_Key). Caliptra reads the i(th) register after setting the DEBUG_AUTH_PK_HASH_REG_BANK_OFFSET. This read operation retrieves the hash of the i(th) level PRE_DEBUG_PK from the appropriate register. Once Caliptra obtains this hash value, it compares it with the hash of the corresponding DEBUG_PK provided through the TAP interface. If the hash comparison is successful, Caliptra proceeds to authenticate the payload using the corresponding DEBUG_PKs.

If either the authentication or the hash comparison fails, Caliptra returns a failure status and updates the Reg_CLPT_to_MCU register in the MailBox to reflect the error. On the other hand, if both the hash comparison and the authentication are successful, Caliptra grants access to production debug mode by writing to the Reg_CLPT_to_MCU register, setting the PROD_DEBUG_EN bit. This action signals that the SoC is now in production debug mode and ready for further operations.

This flow establishes a secure and controlled process for entering Caliptra’s production debug mode, ensuring that only authorized access is granted while maintaining the integrity and confidentiality of the system’s sensitive assets. The more details about the flow sequence as illustrated with flow figure and explanation of each steps in the flow.

*Figure: Caliptra Subsystem Production Debug Life Cycle View*
![](https://github.com/chipsalliance/caliptra-ss/blob/bpillilli-main-spec-md-update/docs/images/Prod-Debug-LifeCycle.png)

1. (Platform) DEBUG_INTENT_STRAP Assertion:
   * The process is initiated when the DEBUG_INTENT_STRAP pin, connected via the SoC's GPIO, is asserted high.
   * When this pin is high and the LCC is in the PROD state, Caliptra HW observes this activity. The DEBUG_INTENT_STRAP can be asserted at any time, but Caliptra handles it in two phases: Pre-ROM Execution and Post-ROM Execution. Based on the timing, the debugger might need to assert BootFSMBrk (if ROM based debug unlock has to be executed).
2. (Caliptra HW) Erasing Secret Assets: Caliptra HW wipes secret assets (Unique Device Secret (UDS) and Field entropy).
3. (Platform over TAP requests) PROD_DEBUG_UNLOCK_REQ: The system intends to be in debug mode for manufacturing services.
4. (Platform over TAP requests) Write to Boot Continue: Resuming the boot process after halting it with BootFSMBrk (CPTRA_BOOTFSM_GO).
5. (Caliptra ROM) Reads PROD_DEBUG_UNLOCK_REQ at optimal time for ROM and clears mailbox lock
6. (Platform over TAP requests) Reads Caliptra mailbox lock. If lock is obtained, then platform over TAP writes Auth Debug Unlock Request DOE object (see the table below) to TAP mailbox.
   * **Auth Debug Unlock Request DOE object:** The debugger sends 24-bits desired unlock category
7. (Caliptra ROM) Reads and parses Auth Debug Unlock Request DOE object
8. (Caliptra ROM) Generates Auth Challenge DoE response object. Generates random 48-byte nonce. Gathers the unique device identifier. Packages them as described in Auth Challenge DoE response object Table. Places Auth
9. (Platform over TAP requests) Reads Places Auth Challenge DoE response
10. (Platform) Asks the authorized server to receive hybrid signature of Auth Challenge DoE response object. The signature payload is called Auth response unlock token (see the table below)
11. (Platform over TAP requests) Writes Auth response unlock token to MailBox Following Steps by Caliptra ROM:
12. **Payload Authentication:**
 * Caliptra ROM asserts PROD_DEBUG_UNLOCK_IN_PROGRESS.
 * Caliptra ROM reads public key indexed with Auth Debug Unlock Request DOE object.
 * Caliptra ROM checks the authentication of Auth response unlock token with this public key.
 * If the authentication fails, Caliptra ROM returns a failure status and reflects it in the PROD_DEBUG_UNLOCK_FAILURE register.
 * Otherwise, PROD_DEBUG_UNLOCK_SUCCESS register will be written.; Caliptra ROM also de-asserts PROD_DEBUG_UNLOCK_IN_PROGRESS register.

**Granting Production Debug Mode:**
* If authentication succeeds, Caliptra ROM does not immediately grant full production debug mode. Instead, the ROM sets the appropriate **"debug level"** signal, which corresponds to the type of debug access being requested.
* Caliptra ROM writes CALIPTRA_SS_SOC_DEBUG_UNLOCK_LEVEL register, which will be wired to the specific debug enable signal. This signal is part of an N-wide signal that is mapped to the payload encoding received during the debug request. N is defined by NUM_OF_ DEBUG_AUTH_PK_HASHES. The default version of N is 8. The payload encoding can either be one-hot encoded or a general encoded format, and this signal is passed to the SoC to allow it to make the final decision about the level of debug access that should be granted. In Caliptra’s subsystem-specific implementation, the logic is configured to handle one-hot encoding for these 8 bits. The level 0 bit is routed to both Caliptra and the MCU TAP interface, allowing them to unlock based on this level of debug access. This granular approach ensures that the system can selectively unlock different levels of debugging capability, depending on the payload and the authorization level provided by the debugger.

## Masking Logic for Debugging Features in Production Debug Mode (MCI)
In the production debug mode, the SoC can enable certain debugging features—such as DFT_EN, SOC_HW_DEBUG_EN, and Caliptra_SS_uCTAP_HW_DEBUG_EN—using a masking mechanism implemented within the Manufacturer Control Interface (MCI). This masking infrastructure allows the SoC to selectively control debug features that are normally gated by Caliptra’s internal signals. The masking logic functions as a set of registers, implemented in the MCI, that can be written by the SoC to override or enable specific debugging functionalities in production debug mode.
The masking registers in the MCI act as an OR gate with the existing debug signals. For instance, if DFT_EN is controlled by Caliptra, the SoC can assert the corresponding mask register to enable Design for Test (DFT) capabilities in the SoC, even if Caliptra has not explicitly enabled it. Similarly, the SOC_HW_DEBUG_EN and Caliptra_SS_uCTAP_HW_DEBUG_EN signals can be masked through the MCI registers, giving the SoC the flexibility to unlock TAP interfaces and provide the required debugging in production.

*Figure: Caliptra Subsystem Infrastructure for SOC flexibility to override various debug signals*
![](https://github.com/chipsalliance/Caliptra/blob/main/doc/images/SOC-Debug-Unlock-Qual.png)

This mechanism is only authorized when both the LCC and Caliptra core are in the PROD state and operating in production debug mode. The masking logic ensures that these features are enabled securely, in line with the production debug flow described in the "SoC Debug Flow and Architecture for Production Mode" section. By leveraging the MCI’s masking infrastructure, the SoC integrator has greater flexibility to implement custom debugging options during production without compromising the security framework established by Caliptra.


## Production Debug Policy Authorization Content

The Caliptra production debug mode architecture supports up to eight distinct categories of debug access, though it is not necessary to utilize all eight. Each category is associated with a unique set of cryptographic keys, offering flexibility and granularity in the debug process. The MCU sends the hash results of up to 8 PRE_DEBUG_PKs to Caliptra, where 8 is the default value and see the definition of NUM_OF_ DEBUG_AUTH_PK_HASHES for more details. These hash values are derived from the public keys corresponding to each debug category and are securely stored in the MCU’s FUSE.

Upon receiving the hash results, Caliptra selects the appropriate PRE_DEBUG_PK hash to compare against the stored DEBUG_PK, determining which debug category is being requested. This selection is made based on the specific debug operation being invoked. Caliptra then authenticates the request using a Hybrid cryptosystem that combines both ECC (Elliptic Curve Cryptography) and MLDSA (PQC Digital Signature Algorithm).
The private keys corresponding to these public keys are stored securely on an external authorization server, ensuring that they remain protected and isolated from the SoC. For each of the eight debug categories, the validity of the public keys is tracked via a valid/invalid bit stored in the FUSE. This bit serves as a key revocation mechanism, allowing keys to be invalidated if necessary, such as when a key is compromised or no longer needed. This revocation system enhances security by ensuring that only valid keys can be used for debug access, preventing unauthorized attempts to enter debug mode.

| **Payload Content** 		|  **Size (Byte)**  |
| :--------- 	      		| :--------- | 
| Marker 			| 4 |
| Hybrid PK (ECC or MLDSA) 	| 2640 |
| Index_Of_Public_Key 		| 4 |
| Unique_Device_ID 		| 32 |
| Message 			| 128 |
| Signature (ECC or MLDSA) 	| 4723 |
| Reserved 			| 1 |
|Total Byte Count 		| 7,532 (~8KB) |


## SOC & Manuf Debug Caliptra Subsystem Hardware Requirements

### Caliptra Requirement List for Production Debug Unlock Architecture

* Wiring DEBUG_INTENT_STRAP to Caliptra debug mode logic to trigger debug preparation·
* Caliptra Mailbox is open to TAP interface to read/write only if DEBUG_INTENT_STRAP is set.
* Separate Request and Response registers exposed for JTAG/TAP access in Debug locked mode and over AXI.
* Functionality to communicate with MCU to ask hashed public key by using “SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET”, “SS_NUM_OF_DEBUG_AUTH_PK_HASHES” (default is 8) and “i” values
* Mailbox command & payloads are defined by Caliptra ROM spec (includes MLDSA and ECC infrastructure for payload commands)
      
### Caliptra Requirement List for Manufacturing Debug Unlock Architecture

* MANUF_DEBUG_REQ allocation for requesting service and MANUF_DEBUG_RSP for responses accessible over TAP and over AXI
* Caliptra Mailbox infrastructure for command, payload and public key authentication (that gets the 256-bit for TOKEN)
* Capability to generate 256-bit Nonce
* Having SHA_512 infrastructure

### MCU and MCI Requirements
* Masking registers to override  DFT_EN, SOC_HW_DEBUG_EN, and Caliptra_SS_uCTAP_HW_DEBUG_EN
* uCTAP Unlock logic
* Caliptra Subsystem’s Boot/Reset Sequencer signals for LCC’s power manager interface
* MCU ROM reading flow for hashed public key and allocate to registers implemented at “SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET” with "SS_NUM_OF_DEBUG_AUTH_PK_HASHES" of PK hashes

### FUSE Requirements
* A public content FUSEs for hashed public keys for SS_NUM_OF_DEBUG_AUTH_PK_HASHES (Default of 8)

## LCC Interpretation for Caliptra “Core” Security States

Caliptra Core has five security states as given with the figure below (Copied from Caliptra core specification). Three of these states enable debugging with different features, while two of these states are in non-debug mode. Caliptra Subsystem implements gasket logic to translate the LCC states to Caliptra “Core” security states.

*Figure: Caliptra Core Security States*
![](https://github.com/chipsalliance/Caliptra/blob/main/doc/images/Caliptra_security_states.png)

This translation is essential for ensuring that the system behaves correctly according to its current lifecycle stage, whether it is in a development phase, production, or end-of-life states.
The LCC provides specific decoding signals—DFT_EN, SOC_HW_DEBUG_EN, and Caliptra_SS_uCTAP_HW_DEBUG_EN—that accommodates the debug capabilities and security states of the Caliptra Core. Depending on the values of these signals, the Caliptra Core transitions between different security states as follows:

**Non-Debug Mode:** This state is enforced when the LCC is in RAW, TEST_LOCKED, SCRAP, INVALID, or POST_TRANSITION states. In these states, the DFT_EN, SOC_HW_DEBUG_EN, and Caliptra_SS_uCTAP_HW_DEBUG_EN signals are all low, ensuring that no debug functionality is available. Caliptra remains in a secure, non-debug state, with no access to debugging interfaces.

**Unprovisioned Debug Mode:** When the LCC is in the TEST_UNLOCKED state, the DFT_EN, SOC_HW_DEBUG_EN, and Caliptra_SS_uCTAP_HW_DEBUG_EN signals are all set high, enabling debug functionality. In this mode, the Caliptra Core allows extensive debugging capabilities, which is typically used during early development and bring-up phases.

**Manufacturing Non-Debug Mode:** This state occurs when the LCC is in the MANUF state, with SOC_HW_DEBUG_EN high and Caliptra_SS_uCTAP_HW_DEBUG_EN low. In this state, the secrets have been programmed into the system, and the Caliptra can generate CSR (Certificate Signing Request) upon request. However, it remains in a secure, non-debug mode to prevent reading secrets through the debugging interfaces.

**Manufacturing Debug Mode:** Also occurring in the MANUF state, this mode is enabled when both SOC_HW_DEBUG_EN and Caliptra_SS_uCTAP_HW_DEBUG_EN are high. Here, the Caliptra Core provides debugging capabilities while maintaining security measures suitable for manufacturing environments.

**Production Non-Debug Mode:** This state is active when the LCC is in the PROD or PROD_END states, with all debug signals (DFT_EN, SOC_HW_DEBUG_EN, and Caliptra_SS_uCTAP_HW_DEBUG_EN) set to low. The Caliptra Core operates in a secure mode with no debug access, suitable for fully deployed production environments.

**Production Debug Mode:** This state is active when the LCC is in the PROD state, with debug DFT_EN, SOC_HW_DEBUG_EN set to low, and Caliptra_SS_uCTAP_HW_DEBUG_EN is high. Caliptra Core provides debugging capabilities while maintaining security measures suitable for manufacturing environments.

**Production Debug Mode in RMA:** In the RMA state, all debug signals are set high, allowing full debugging access. This state is typically used for end-of-life scenarios where detailed inspection of the system's operation is required. However, the LCC is not standalone enough to put Caliptra into production debug mode. Steps described in SoC Debug Flow and Architecture for Production Mode Section should be followed.

The table below summarizes the relationship between the LCC state, the decoder output signals, and the resulting Caliptra “Core” security state:

*Table: LCC state translation to Caliptra "Core" security states*

| **LCC State vs Decoder Output** 	| **DFT_EN** 	| **SOC_HW_DEBUG_EN** 	| **Caliptra_SS_uCTAP_HW_DEBUG_EN** 	| **Caliptra “Core” Security States** |
| :--------- 	      			| :--------- 	| :--------- 	      	| :---------  				| :--------- |
| RAW 					| Low 		| Low 			|  Low 					| Non-Debug |
| TEST_LOCKED 				| Low 		| Low 			|  Low 					| Non-Debug |
| TEST_UNLOCKED  			| High  	| High	 		|  High 				| Unprovisioned Debug |
| MANUF 				| Low 		| High 			|  Low 					| Manuf Non-Debug |
| MANUF* 				| Low 		| High 			|  High 				| Manuf Debug |
| PROD 					| Low 		| Low 			|  Low 					| Prod Non-Debug |
| PROD* 				| Low** 	| High** 		|  High 				| Prod Debug |
| PROD_END 				| Low 		| Low 			|  Low 					| Prod Non-Debug |
| RMA 					| High 		| High 			|  High					| Prod Debug |
| SCRAP 				| Low 		| Low 			|  Low 					| Non-Debug |
| INVALID 				| Low 		| Low 			|  Low 					| Non-Debug |
| POST_TRANSITION 			| Low 		| Low 			|  Low 					| Prod Non-Debug |

**Note:** In RAW, TEST_LOCKED, SCRAP and INVALID states, Caliptra “Core” is not brought out of reset.
*: These states are Caliptra SS’s extension to LCC. Although the LCC is in either MANUF or PROD states, Caliptra core can grant debug mode through the logics explained in “How does Caliptra enable uCTAP_UNLOCK?” and “SoC Debug Flow and Architecture for Production Mode”. 
**: SOC_HW_DEBUG_EN and DFT_EN can be overridden by SoC support in PROD state.

## SOC LCC Interface usage & requirements

The interaction between the SoC and the LCC within the Caliptra Subsystem is pivotal for maintaining the security and functionality of the overall system. This section outlines the specific usage and requirements for interfacing with the LCC from the SoC perspective.

**SOC_HW_DEBUG_EN Utilization:** The SOC_HW_DEBUG_EN signal plays a crucial role in controlling access to the Chip-Level TAP (CLTAP). When SOC_HW_DEBUG_EN is asserted high, it enables the exposure of registers to the TAP interface that are deemed secure for access during debugging. This is particularly important when CLTAP is open, as it allows authorized debugging operations while ensuring that sensitive or secure information remains protected.

**uController TAPs Debug Access:** For security reasons, SoCs must restrict access to their uCTAPs. These TAPs should only be opened for debugging when the Caliptra_SS_uCTAP_HW_DEBUG_EN signal, driven by the Caliptra, is set high. This ensures that debug access is only permitted under controlled conditions, typically during development or when specific secure transitions are in place.

**LCC Outputs for Security/Debug Purposes:** Beyond the primary debug controls, all other LCC outputs, as listed in the signal table below, are available for use by the SoC for any security or debugging purposes. These outputs provide the SoC with additional control signals that can be leveraged to enhance system security, monitor debug operations, or implement custom security features.

**Integration with Clock/Voltage Monitoring Logic:** If the SoC includes clock or voltage monitoring logic, it is recommended that these components be connected to the LCC's alert handling interface. By integrating with the LCC’s alert system, the SoC can ensure that any detected anomalies, such as voltage fluctuations or clock inconsistencies, trigger appropriate secure transitions as defined in [this document](https://opentitan.org/book/hw/ip/lc_ctrl/doc/theory_of_operation.html). This connection enhances the overall security posture by enabling the LCC to respond dynamically to potential threats or system irregularities.

These requirements ensure that the SoC and LCC work in tandem to maintain a secure environment, particularly during debugging and system monitoring. By adhering to these guidelines, the SoC can leverage the LCC’s capabilities to protect sensitive operations and enforce security policies across the system.

## LCC Module: Summarized Theory of operation

The LCC is designed to handle the various life-cycle states of the device, from initial provisioning through manufacturing to production and eventual decommissioning (RMA). It provides mechanisms for state transitions, secure key management, and debug control, ensuring that the device operates securely throughout its lifecycle. For more information, please refer to the [Life-cycle controller documentation](https://opentitan.org/book/hw/ip/lc_ctrl/doc/theory_of_operation.html). While the LCC is reused from OpenTitan, Caliptra Subsystem’s security & debug architecture has some differences. Therefore, Subsystem implements the functions required to meet Caliptra specific requirements.

LCC has the same power up sequence as described in Life cycle controller documentation of [OpenTitan open-source silicon Root of Trust (RoT) project](https://opentitan.org/book/hw/ip/lc_ctrl/doc/theory_of_operation.html). After completing the power up sequence, the LCC enters the normal operation routine. During this phase, its output remains static unless specifically requested to change. The LCC accepts life-cycle transition change requests from its TAP interface (TAP Pin Muxing). There are two types of state transitions: (i) unconditional transitions and (ii) conditional transitions.

For unconditional transitions, the LCC advances the state by requesting an OTP update to the FUSE controller. Once the programming is confirmed, the life cycle controller reports a success to the requesting agent and waits for the device to reboot.

For conditional transitions, the LCC can also branch different states (RAW_UNLOCK, TEST_UNLOCK, TEST_EXIT, RMA_UNLOCK) based on the received token through the TAP interface and compared the received tokens against the ones stored in FUSE . This branching is called conditional transitions. For more information about the conditional states, please refer to [OpenTitan open-source silicon Root of Trust (RoT) project](https://opentitan.org/book/hw/ip/lc_ctrl/doc/theory_of_operation.html).

**Notes:**
* Some tokens are hardcoded design constants (specifically for RAW to TEST_UNLOCK), while others are stored in FUSE.
* Conditional transitions will only be allowed if the FUSE partition holding the corresponding token has been provisioned and locked.
* For transition counter limits and token hashing mechanism, please refer to OpenTitan open-source silicon Root of Trust (RoT) project  [1].
* The LCC enters the post transition handling routine after completing conditional and unconditional transitions. During this routine, the LCC disables all of its decoded outputs and puts the system in an inert state.


# Manufacturer Control Unit (MCU)

# Manufacturer Control Interface (MCI)

# Subsystem Memory Map

# Subsystem HW Security
