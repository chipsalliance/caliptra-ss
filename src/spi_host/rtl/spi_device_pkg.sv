// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Device module.
//

`include "caliptra_prim_assert.sv"

package caliptra_ss_spi_device_pkg;

  // Passthrough Inter-module signals
  typedef struct packed {
    // passthrough_en: switch the mux for downstream SPI pad to host system not
    // the internal SPI_HOST IP
    logic       passthrough_en;

    // Passthrough includes SCK also. The sck_en is pad out enable not CG
    // enable. The CG is placed in SPI_DEVICE IP.
    logic       sck;
    logic       sck_en;

    // CSb should be pull-up pad. In passthrough mode, CSb is directly connected
    // to the host systems CSb except when SPI_DEVICE decides to drop the
    // command.
    logic       csb;
    logic       csb_en;

    // SPI data from host system to downstream flash device.
    logic [3:0] s;
    logic [3:0] s_en;
  } caliptra_ss_passthrough_req_t;

  typedef struct packed {
    // SPI data from downstream flash device to host system.
    logic [3:0] s;
  } caliptra_ss_passthrough_rsp_t;

endpackage : caliptra_ss_spi_device_pkg
