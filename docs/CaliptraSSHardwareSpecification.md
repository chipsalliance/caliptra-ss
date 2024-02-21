![OCP Logo](./images/OCP_logo.png)

<p style="text-align: center;">Caliptra Subsystem Hardware Specification</p>

<p style="text-align: center;">Version 0.1</p>

<div style="page-break-after: always"></div>

# Scope

This document defines technical specifications for a reference subsystem design utilizing Caliptra RoT for Measurement (RTM). This document, along with [Caliptra Hardware Specification](https://github.com/chipsalliance/caliptra-rtl/blob/main/docs/CaliptraHardwareSpecification.md), shall comprise the Caliptra Subsystem technical specification.

# Overview

This document provides definitions and requirements for the components used specifically for the subsystem. For specifications of the components re-used from Caliptra RTM, see the [Caliptra Hardware Specification](https://github.com/chipsalliance/caliptra-rtl/blob/main/docs/CaliptraHardwareSpecification.md).

# Caliptra Manufacturer Control Unit

The Caliptra Manufacturer Control Unit (MCU) repurposes a subset of the Caliptra RTM design. The MCU is intended to run manufacturer specific firmware that will interface with Caliptra to authenticate, measure and load all of the SoC firmware. The MCU firmware is also responsible for performing SoC specific initializations, and should be able to toggle functional signals and resets specific to the SoC.
In addition to the peripherals leveraged from Caliptra RTM design, the subsystem includes an I3C peripheral for loading firmware, an AXI command buffer that initiates transactions onto the SoC fabric for communication with Caliptra as well as loading firmware to other SoC peripherals, and a custom fuse controller block for handling Caliptra and subsystem specific fuses.

# I3C

Development of I3C is WIP.

# AXI Command Buffer

The AXI Command Buffer utilizes a 64B data buffer and a set of command API registers to initiate read and write transactions onto the SoC fabric using AXI protocol. The MCU programs the address and command type for the requested transaction and populates the data buffer for write transactions before setting a GO register that will initiate the transaction. Read transactions will store their return data in the data buffer.

## API



# Fuse Controller

Development of Fuse Controller is WIP.
