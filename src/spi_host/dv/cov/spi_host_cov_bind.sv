// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds SPI Host functional coverage interface to caliptra_ss_spi_host module.
module spi_host_cov_bind;

  bind caliptra_ss_spi_host spi_host_cov_if #(
    .NumCS(NumCS)
  ) u_spi_cov_if (
    .clk_i           (clk_i),
    .rst_ni          (rst_ni),
    .cio_sck_o       (cio_sck_o),
    .cio_sck_en_o    (cio_sck_en_o),
    .cio_csb_o       (cio_csb_o),
    .cio_csb_en_o    (cio_csb_en_o),
    .cio_sd_o        (cio_sd_o),
    .cio_sd_en_o     (cio_sd_en_o),
    .cio_sd_i        (cio_sd_i),
    .intr_error_o    (intr_error_o),
    .intr_spi_event_o(intr_spi_event_o)
  );

endmodule
