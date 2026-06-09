# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Example SPI host SDC constraints for 400 MHz system clock and 50 MHz SPI clock targeting an
# off-the-shelf SPI flash chip. Other SPI targets *will* require a different set of constraints.

###############
## Constants ##
###############

# Represents approximately 5 inches of trace
set PCB_DEL 0.85

# Max skew between signals. Represents approximately 3 inches.
set PCB_SKEW 0.51

# External SPI device setup and hold (depends on the target SPI device)
set STORAGE_SETUP_DEL 2
set STORAGE_HOLD_DEL -3

# External SPI device clk-to-q (depends on the target SPI device)
set STORAGE_OUT_DEL_MIN 0
set STORAGE_OUT_DEL_MAX 7


#########
## SoC ##
#########

# Main clock
create_clock [get_ports clk_i] -name CLK -period 2.5

# Output delays
set_input_delay  -max -add_delay -clock CLK  1.25 [get_ports {rst_ni}]
set_input_delay  -max -add_delay -clock CLK  0.10 [get_ports {s_axi_*_i*}]
set_output_delay -max -add_delay -clock CLK  0.10 [get_ports {s_axi_*_o*}]
set_output_delay -max -add_delay -clock CLK  0.10 [get_ports {intg_error_o}]
set_output_delay -max -add_delay -clock CLK  0.10 [get_ports {intr_error_o}]
set_output_delay -max -add_delay -clock CLK  0.10 [get_ports {intr_spi_event_o}]


##############
## SPI Host ##
##############

# See https://docs.google.com/drawings/d/1qkUnXaRafIPyBnVpreqfbF_zSy0xlpHqXMZp6F-j8Cc/edit?usp=sharing
# During pre-layout, the SPI_CLK source latencies are estimated to account
# for pad and logic latencies. After CTS, source latency must be removed as all
# clocks are propagated.

# Generated SPI clock of 50 MHz. 50MHz is chosen for purposes of timing closure as it is the highest
# permitted clock frequency in these constraints.
create_generated_clock -name SPI_CLK -source [get_ports {clk_i}] -divide_by 8 [get_ports cio_sck_o] -master_clock CLK -add

# Multi-cycle path to adjust the hold edge, since launch and capture edges are
# opposite in the SPI_CLK domain.
set_multicycle_path -setup 1 -start -from [get_clocks CLK] -to [get_clocks SPI_CLK]
set_multicycle_path -hold  1 -start -from [get_clocks CLK] -to [get_clocks SPI_CLK]

# Set multicycle path for data going from SPI_CLK to logic
# the SPI host logic will read these paths at "full cycle"
set_multicycle_path -setup 6 -end -from [get_clocks SPI_CLK] -to [get_clocks CLK]
set_multicycle_path -hold 1  -end -from [get_clocks SPI_CLK] -to [get_clocks CLK]

# Computed delays from connected device
# host in has 2x the PCB delay to account for delays on both outgoing clocks and incoming data
set SPI_HOST_OUT_DEL_MIN [expr ${STORAGE_HOLD_DEL}  - ${PCB_SKEW}]
set SPI_HOST_OUT_DEL_MAX [expr ${STORAGE_SETUP_DEL} + ${PCB_SKEW}]
set SPI_HOST_IN_DEL_MIN  [expr ${STORAGE_OUT_DEL_MIN}]
set SPI_HOST_IN_DEL_MAX  [expr ${STORAGE_OUT_DEL_MAX} + 2 * ${PCB_DEL}]

# Bidir ports, with the downstream device launching on falling edge. Our example device operates in
# SPI mode 0 (CPOL=0, CPHA=0).
set_input_delay  -min ${SPI_HOST_IN_DEL_MIN} [get_ports "cio_sd_io*"] -clock_fall -clock SPI_CLK -add_delay
set_input_delay  -max ${SPI_HOST_IN_DEL_MAX} [get_ports "cio_sd_io*"] -clock_fall -clock SPI_CLK -add_delay
set_output_delay -min ${SPI_HOST_OUT_DEL_MIN} [get_ports "cio_sd_io* cio_csb_o*"] -clock SPI_CLK -add_delay
set_output_delay -max ${SPI_HOST_OUT_DEL_MAX} [get_ports "cio_sd_io* cio_csb_o*"] -clock SPI_CLK -add_delay
