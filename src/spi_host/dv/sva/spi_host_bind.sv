// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module spi_host_bind;

  bind caliptra_ss_spi_host tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  // Note: OpenTitan FPV CSR assertion generator is not packaged in Caliptra-SS.
  // CSR reset, RW, bit-bash, aliasing, and bus-integrity checks run in UVM.

  bind caliptra_ss_spi_host spi_host_data_stable_sva #(
    .NumCS(spi_host_env_cfg_pkg::SPI_HOST_NUM_CS)
  ) spi_host_data_stable_assert (
    .clk_i,
    .rst_ni,
    .active_i      (active),
    .cio_sck_o,
    .cio_csb_o,
    .cio_sd_o,
    .cio_sd_i,
    .cio_sd_en_o,
    .fsm_cpol_i    (u_spi_core.u_fsm.cpol_q),
    .fsm_cpha_i    (u_spi_core.u_fsm.cpha_q),
    .fsm_full_cyc_i(u_spi_core.u_fsm.full_cyc_q),
    .passthrough_i
  );

endmodule
