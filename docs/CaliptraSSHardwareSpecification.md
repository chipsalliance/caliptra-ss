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

# QSPI

# I3C

# AXI Command Buffer

# Fuse Controller

