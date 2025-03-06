
# Default settings:
set BUILD FALSE
set GUI   FALSE
set JTAG  FALSE
set ITRNG FALSE
set CG_EN FALSE
set RTL_VERSION latest

# TODO: This is a hacky way of quickly switching between the Zynq and Versal boards
#set BOARD ZCU104
#set DISABLE_ECC TRUE
#set ENABLE_ADB FALSE
#set ITRNG FALSE

set BOARD VCK190
set DISABLE_ECC FALSE
set ENABLE_ADB TRUE
set ITRNG TRUE

set I3C_OUTSIDE FALSE
set APB FALSE
# Simplistic processing of command line arguments to override defaults
foreach arg $argv {
    regexp {(.*)=(.*)} $arg fullmatch option value
    set $option "$value"
}
# If VERSION was not set by tclargs, set it from the commit ID.
# This assumes it is run from within caliptra-sw. If building from outside caliptra-sw call with "VERSION=[hex number]"
if {[info exists VERSION] == 0} {
  set VERSION [exec git rev-parse --short HEAD]
}

# Create path variables
set fpgaDir [file dirname [info script]]
if {$BOARD eq "ZCU104"} {
  set outputDir $fpgaDir/caliptra_build
} else {
  set outputDir $fpgaDir/caliptra_build_versal
}
set caliptrapackageDir $outputDir/caliptra_package
set sspackageDir $outputDir/ss_package
# Clean and create output directory.
file delete -force $outputDir
file mkdir $outputDir
file mkdir $caliptrapackageDir
file mkdir $sspackageDir

# Path to rtl
#set rtlDir $fpgaDir/../$RTL_VERSION/rtl
set caliptrartlDir $fpgaDir/../third_party/caliptra-rtl
set ssrtlDir $fpgaDir/..
puts "JTAG: $JTAG"
puts "ITRNG: $ITRNG"
puts "CG_EN: $CG_EN"
puts "RTL_VERSION: $RTL_VERSION"
puts "Using RTL directory $caliptrartlDir"

# Set Verilog defines for:
#     Caliptra clock gating module
#     VEER clock gating module
#     VEER core FPGA optimizations (disables clock gating)
if {$CG_EN} {
  set VERILOG_OPTIONS {TECH_SPECIFIC_ICG USER_ICG=fpga_real_icg TECH_SPECIFIC_EC_RV_ICG USER_EC_RV_ICG=fpga_rv_clkhdr}
  set GATED_CLOCK_CONVERSION auto
} else {
  set VERILOG_OPTIONS {TECH_SPECIFIC_ICG USER_ICG=fpga_fake_icg RV_FPGA_OPTIMIZE TEC_RV_ICG=clockhdr}
  set GATED_CLOCK_CONVERSION off
}
if {$ITRNG} {
  # Add option to use Caliptra's internal TRNG instead of ETRNG
  lappend VERILOG_OPTIONS CALIPTRA_INTERNAL_TRNG
}
if {$APB} {
  lappend VERILOG_OPTIONS CALIPTRA_APB
}
if {$I3C_OUTSIDE} {
  lappend VERILOG_OPTIONS I3C_OUTSIDE
}
lappend VERILOG_OPTIONS FPGA_VERSION=32'h$VERSION
lappend VERILOG_OPTIONS DIGITAL_IO_I3C

# Start the Vivado GUI for interactive debug
if {$GUI} {
  start_gui
}

if {$BOARD eq "ZCU104"} {
  set PART xczu7ev-ffvc1156-2-e
} elseif {$BOARD eq "VCK190"} {
  set PART xcvc1902-vsva2197-2MP-e-S
} else {
  puts "Board $BOARD not supported"
  exit
}

##### MCU Package #####
#source create_mcu_package.tcl
##### MCU Package #####

##### Caliptra Package #####
source create_caliptra_package.tcl
##### Caliptra Package #####


# Create a project for the SOC connections
create_project caliptra_fpga_project $outputDir -part $PART

# Include the packaged IP
set_property  ip_repo_paths  "$caliptrapackageDir $sspackageDir" [current_project]
update_ip_catalog

# Create SOC block design
create_bd_design "caliptra_fpga_project_bd"

# Add Caliptra package
create_bd_cell -type ip -vlnv design:user:caliptra_package_top:1.0 caliptra_package_top_0

# Add Zynq/Versal PS
if {$BOARD eq "ZCU104"} {
  create_bd_cell -type ip -vlnv xilinx.com:ip:zynq_ultra_ps_e ps_0
  set_property -dict [list \
    CONFIG.PSU__CRL_APB__PL0_REF_CTRL__FREQMHZ {20} \
    CONFIG.PSU__USE__IRQ0 {1} \
    CONFIG.PSU__GPIO_EMIO__PERIPHERAL__ENABLE {1} \
    CONFIG.PSU__GPIO_EMIO__PERIPHERAL__IO {5} \
  ] [get_bd_cells ps_0]

  # Create variables to adapt between PS
  set ps_m_axi ps_0/M_AXI_HPM0_LPD
  set ps_pl_clk ps_0/pl_clk0
  set ps_axi_aclk ps_0/maxihpm0_lpd_aclk
  set ps_pl_resetn ps_0/pl_resetn0
  set ps_gpio_i ps_0/emio_gpio_i
  set ps_gpio_o ps_0/emio_gpio_o

  # Create XDC file with constraints
  set xdc_fd [ open $outputDir/jtag_constraints.xdc w ]
  puts $xdc_fd {create_clock -period 5000.000 -name {jtag_clk} -waveform {0.000 2500.000} [get_pins {caliptra_fpga_project_bd_i/ps_0/inst/PS8_i/EMIOGPIOO[0]}]}
  puts $xdc_fd {set_clock_groups -asynchronous -group [get_clocks {jtag_clk}]}
  close $xdc_fd

} else {
  # Create interface ports
  set ddr4_dimm1 [ create_bd_intf_port -mode Master -vlnv xilinx.com:interface:ddr4_rtl:1.0 ddr4_dimm1 ]

  set ddr4_dimm1_sma_clk [ create_bd_intf_port -mode Slave -vlnv xilinx.com:interface:diff_clock_rtl:1.0 ddr4_dimm1_sma_clk ]
  set_property -dict [ list \
   CONFIG.FREQ_HZ {200000000} \
   ] $ddr4_dimm1_sma_clk

  create_bd_cell -type ip -vlnv xilinx.com:ip:versal_cips ps_0
  set_property -dict [list \
    CONFIG.CLOCK_MODE {Custom} \
    CONFIG.DDR_MEMORY_MODE {Enable} \
    CONFIG.DEBUG_MODE {JTAG} \
    CONFIG.DESIGN_MODE {1} \
    CONFIG.PS_PL_CONNECTIVITY_MODE {Custom} \
    CONFIG.PS_PMC_CONFIG { \
      CLOCK_MODE {Custom} \
      DDR_MEMORY_MODE {Connectivity to DDR via NOC} \
      DEBUG_MODE {JTAG} \
      DESIGN_MODE {1} \
      PMC_CRP_PL0_REF_CTRL_FREQMHZ {20} \
      PMC_CRP_PL1_REF_CTRL_FREQMHZ {200} \
      PMC_GPIO0_MIO_PERIPHERAL {{ENABLE 1} {IO {PMC_MIO 0 .. 25}}} \
      PMC_GPIO1_MIO_PERIPHERAL {{ENABLE 1} {IO {PMC_MIO 26 .. 51}}} \
      PMC_MIO37 {{AUX_IO 0} {DIRECTION out} {DRIVE_STRENGTH 8mA} {OUTPUT_DATA high} {PULL pullup} {SCHMITT 0} {SLEW slow} {USAGE GPIO}} \
      PMC_OSPI_PERIPHERAL {{ENABLE 0} {IO {PMC_MIO 0 .. 11}} {MODE Single}} \
      PMC_QSPI_COHERENCY {0} \
      PMC_QSPI_FBCLK {{ENABLE 1} {IO {PMC_MIO 6}}} \
      PMC_QSPI_PERIPHERAL_DATA_MODE {x4} \
      PMC_QSPI_PERIPHERAL_ENABLE {1} \
      PMC_QSPI_PERIPHERAL_MODE {Dual Parallel} \
      PMC_REF_CLK_FREQMHZ {33.3333} \
      PMC_SD1 {{CD_ENABLE 1} {CD_IO {PMC_MIO 28}} {POW_ENABLE 1} {POW_IO {PMC_MIO 51}} {RESET_ENABLE 0} {RESET_IO {PMC_MIO 12}} {WP_ENABLE 0} {WP_IO {PMC_MIO 1}}} \
      PMC_SD1_COHERENCY {0} \
      PMC_SD1_DATA_TRANSFER_MODE {8Bit} \
      PMC_SD1_PERIPHERAL {{CLK_100_SDR_OTAP_DLY 0x3} {CLK_200_SDR_OTAP_DLY 0x2} {CLK_50_DDR_ITAP_DLY 0x36} {CLK_50_DDR_OTAP_DLY 0x3} {CLK_50_SDR_ITAP_DLY 0x2C} {CLK_50_SDR_OTAP_DLY 0x4} {ENABLE 1} {IO\
{PMC_MIO 26 .. 36}}} \
      PMC_SD1_SLOT_TYPE {SD 3.0} \
      PMC_USE_PMC_NOC_AXI0 {1} \
      PS_CAN1_PERIPHERAL {{ENABLE 1} {IO {PMC_MIO 40 .. 41}}} \
      PS_CRL_CAN1_REF_CTRL_FREQMHZ {160} \
      PS_ENET0_MDIO {{ENABLE 1} {IO {PS_MIO 24 .. 25}}} \
      PS_ENET0_PERIPHERAL {{ENABLE 1} {IO {PS_MIO 0 .. 11}}} \
      PS_ENET1_PERIPHERAL {{ENABLE 1} {IO {PS_MIO 12 .. 23}}} \
      PS_GEN_IPI0_ENABLE {1} \
      PS_GEN_IPI0_MASTER {A72} \
      PS_GEN_IPI1_ENABLE {1} \
      PS_GEN_IPI2_ENABLE {1} \
      PS_GEN_IPI3_ENABLE {1} \
      PS_GEN_IPI4_ENABLE {1} \
      PS_GEN_IPI5_ENABLE {1} \
      PS_GEN_IPI6_ENABLE {1} \
      PS_GPIO_EMIO_PERIPHERAL_ENABLE {1} \
      PS_GPIO_EMIO_WIDTH {5} \
      PS_HSDP_EGRESS_TRAFFIC {JTAG} \
      PS_HSDP_INGRESS_TRAFFIC {JTAG} \
      PS_HSDP_MODE {NONE} \
      PS_I2C0_PERIPHERAL {{ENABLE 1} {IO {PMC_MIO 46 .. 47}}} \
      PS_I2C1_PERIPHERAL {{ENABLE 1} {IO {PMC_MIO 44 .. 45}}} \
      PS_MIO19 {{AUX_IO 0} {DIRECTION in} {DRIVE_STRENGTH 8mA} {OUTPUT_DATA default} {PULL disable} {SCHMITT 0} {SLEW slow} {USAGE Reserved}} \
      PS_MIO21 {{AUX_IO 0} {DIRECTION in} {DRIVE_STRENGTH 8mA} {OUTPUT_DATA default} {PULL disable} {SCHMITT 0} {SLEW slow} {USAGE Reserved}} \
      PS_MIO7 {{AUX_IO 0} {DIRECTION in} {DRIVE_STRENGTH 8mA} {OUTPUT_DATA default} {PULL disable} {SCHMITT 0} {SLEW slow} {USAGE Reserved}} \
      PS_MIO9 {{AUX_IO 0} {DIRECTION in} {DRIVE_STRENGTH 8mA} {OUTPUT_DATA default} {PULL disable} {SCHMITT 0} {SLEW slow} {USAGE Reserved}} \
      PS_NUM_FABRIC_RESETS {1} \
      PS_PCIE_EP_RESET1_IO {None} \
      PS_PCIE_EP_RESET2_IO {None} \
      PS_PCIE_RESET {{ENABLE 1}} \
      PS_PL_CONNECTIVITY_MODE {Custom} \
      PS_UART0_PERIPHERAL {{ENABLE 1} {IO {PMC_MIO 42 .. 43}}} \
      PS_USB3_PERIPHERAL {{ENABLE 1} {IO {PMC_MIO 13 .. 25}}} \
      PS_USE_FPD_AXI_NOC0 {1} \
      PS_USE_FPD_AXI_NOC1 {1} \
      PS_USE_FPD_CCI_NOC {1} \
      PS_USE_FPD_CCI_NOC0 {1} \
      PS_USE_M_AXI_FPD {1} \
      PS_USE_NOC_LPD_AXI0 {1} \
      PS_USE_PMCPL_CLK0 {1} \
      PS_USE_PMCPL_CLK1 {0} \
      PS_USE_PMCPL_CLK2 {0} \
      PS_USE_PMCPL_CLK3 {0} \
      SMON_ALARMS {Set_Alarms_On} \
      SMON_ENABLE_TEMP_AVERAGING {0} \
      SMON_TEMP_AVERAGING_SAMPLES {0} \
    } \
  ] [get_bd_cells ps_0]
  set_property CONFIG.PS_PMC_CONFIG { \
      CLOCK_MODE {Custom} \
      DDR_MEMORY_MODE {Connectivity to DDR via NOC} \
      DEBUG_MODE {JTAG} \
      DESIGN_MODE {1} \
      PMC_CRP_PL0_REF_CTRL_FREQMHZ {20} \
      PMC_CRP_PL1_REF_CTRL_FREQMHZ {100} \
      PMC_GPIO0_MIO_PERIPHERAL {{ENABLE 1} {IO {PMC_MIO 0 .. 25}}} \
      PMC_GPIO1_MIO_PERIPHERAL {{ENABLE 1} {IO {PMC_MIO 26 .. 51}}} \
      PMC_MIO37 {{AUX_IO 0} {DIRECTION out} {DRIVE_STRENGTH 8mA} {OUTPUT_DATA high} {PULL pullup} {SCHMITT 0} {SLEW slow} {USAGE GPIO}} \
      PMC_OSPI_PERIPHERAL {{ENABLE 0} {IO {PMC_MIO 0 .. 11}} {MODE Single}} \
      PMC_QSPI_COHERENCY {0} \
      PMC_QSPI_FBCLK {{ENABLE 1} {IO {PMC_MIO 6}}} \
      PMC_QSPI_PERIPHERAL_DATA_MODE {x4} \
      PMC_QSPI_PERIPHERAL_ENABLE {1} \
      PMC_QSPI_PERIPHERAL_MODE {Dual Parallel} \
      PMC_REF_CLK_FREQMHZ {33.3333} \
      PMC_SD1 {{CD_ENABLE 1} {CD_IO {PMC_MIO 28}} {POW_ENABLE 1} {POW_IO {PMC_MIO 51}} {RESET_ENABLE 0} {RESET_IO {PMC_MIO 12}} {WP_ENABLE 0} {WP_IO {PMC_MIO 1}}} \
      PMC_SD1_COHERENCY {0} \
      PMC_SD1_DATA_TRANSFER_MODE {8Bit} \
      PMC_SD1_PERIPHERAL {{CLK_100_SDR_OTAP_DLY 0x3} {CLK_200_SDR_OTAP_DLY 0x2} {CLK_50_DDR_ITAP_DLY 0x36} {CLK_50_DDR_OTAP_DLY 0x3} {CLK_50_SDR_ITAP_DLY 0x2C} {CLK_50_SDR_OTAP_DLY 0x4} {ENABLE 1} {IO {PMC_MIO 26 .. 36}}} \
      PMC_SD1_SLOT_TYPE {SD 3.0} \
      PMC_USE_PMC_NOC_AXI0 {1} \
      PS_CAN1_PERIPHERAL {{ENABLE 1} {IO {PMC_MIO 40 .. 41}}} \
      PS_CRL_CAN1_REF_CTRL_FREQMHZ {160} \
      PS_ENET0_MDIO {{ENABLE 1} {IO {PS_MIO 24 .. 25}}} \
      PS_ENET0_PERIPHERAL {{ENABLE 1} {IO {PS_MIO 0 .. 11}}} \
      PS_ENET1_PERIPHERAL {{ENABLE 1} {IO {PS_MIO 12 .. 23}}} \
      PS_GEN_IPI0_ENABLE {1} \
      PS_GEN_IPI0_MASTER {A72} \
      PS_GEN_IPI1_ENABLE {1} \
      PS_GEN_IPI2_ENABLE {1} \
      PS_GEN_IPI3_ENABLE {1} \
      PS_GEN_IPI4_ENABLE {1} \
      PS_GEN_IPI5_ENABLE {1} \
      PS_GEN_IPI6_ENABLE {1} \
      PS_GPIO_EMIO_PERIPHERAL_ENABLE {1} \
      PS_GPIO_EMIO_WIDTH {5} \
      PS_HSDP_EGRESS_TRAFFIC {JTAG} \
      PS_HSDP_INGRESS_TRAFFIC {JTAG} \
      PS_HSDP_MODE {NONE} \
      PS_I2C0_PERIPHERAL {{ENABLE 1} {IO {PMC_MIO 46 .. 47}}} \
      PS_I2C1_PERIPHERAL {{ENABLE 1} {IO {PMC_MIO 44 .. 45}}} \
      PS_MIO19 {{AUX_IO 0} {DIRECTION in} {DRIVE_STRENGTH 8mA} {OUTPUT_DATA default} {PULL disable} {SCHMITT 0} {SLEW slow} {USAGE Reserved}} \
      PS_MIO21 {{AUX_IO 0} {DIRECTION in} {DRIVE_STRENGTH 8mA} {OUTPUT_DATA default} {PULL disable} {SCHMITT 0} {SLEW slow} {USAGE Reserved}} \
      PS_MIO7 {{AUX_IO 0} {DIRECTION in} {DRIVE_STRENGTH 8mA} {OUTPUT_DATA default} {PULL disable} {SCHMITT 0} {SLEW slow} {USAGE Reserved}} \
      PS_MIO9 {{AUX_IO 0} {DIRECTION in} {DRIVE_STRENGTH 8mA} {OUTPUT_DATA default} {PULL disable} {SCHMITT 0} {SLEW slow} {USAGE Reserved}} \
      PS_NUM_FABRIC_RESETS {1} \
      PS_PCIE_EP_RESET1_IO {None} \
      PS_PCIE_EP_RESET2_IO {None} \
      PS_PCIE_RESET {{ENABLE 1}} \
      PS_PL_CONNECTIVITY_MODE {Custom} \
      PS_UART0_PERIPHERAL {{ENABLE 1} {IO {PMC_MIO 42 .. 43}}} \
      PS_USB3_PERIPHERAL {{ENABLE 1} {IO {PMC_MIO 13 .. 25}}} \
      PS_USE_FPD_AXI_NOC0 {1} \
      PS_USE_FPD_AXI_NOC1 {1} \
      PS_USE_FPD_CCI_NOC {1} \
      PS_USE_FPD_CCI_NOC0 {1} \
      PS_USE_M_AXI_FPD {1} \
      PS_USE_NOC_LPD_AXI0 {1} \
      PS_USE_PMCPL_CLK0 {1} \
      PS_USE_PMCPL_CLK1 {1} \
      PS_USE_PMCPL_CLK2 {0} \
      PS_USE_PMCPL_CLK3 {0} \
      SMON_ALARMS {Set_Alarms_On} \
      SMON_ENABLE_TEMP_AVERAGING {0} \
      SMON_TEMP_AVERAGING_SAMPLES {0} \
} [get_bd_cells ps_0]
#TODO fix the above

  # Create instance: axi_noc_0, and set properties
  set axi_noc_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_noc axi_noc_0 ]
  set_property -dict [ list \
   CONFIG.CONTROLLERTYPE {DDR4_SDRAM} \
    CONFIG.MC0_CONFIG_NUM {config17} \
    CONFIG.MC1_CONFIG_NUM {config17} \
    CONFIG.MC2_CONFIG_NUM {config17} \
    CONFIG.MC3_CONFIG_NUM {config17} \
    CONFIG.MC_CASLATENCY {22} \
    CONFIG.MC_CHAN_REGION1 {DDR_LOW1} \
    CONFIG.MC_COMPONENT_WIDTH {x8} \
    CONFIG.MC_CONFIG_NUM {config17} \
    CONFIG.MC_DATAWIDTH {64} \
    CONFIG.MC_DDR4_2T {Disable} \
    CONFIG.MC_F1_TRCD {13750} \
    CONFIG.MC_F1_TRCDMIN {13750} \
    CONFIG.MC_INPUTCLK0_PERIOD {5000} \
    CONFIG.MC_MEMORY_DEVICETYPE {UDIMMs} \
    CONFIG.MC_MEMORY_SPEEDGRADE {DDR4-3200AA(22-22-22)} \
    CONFIG.MC_NO_CHANNELS {Single} \
    CONFIG.MC_RANK {1} \
    CONFIG.MC_ROWADDRESSWIDTH {16} \
    CONFIG.MC_STACKHEIGHT {1} \
    CONFIG.MC_SYSTEM_CLOCK {Differential} \
    CONFIG.MC_TRC {45750} \
    CONFIG.MC_TRCD {13750} \
    CONFIG.MC_TRCDMIN {13750} \
    CONFIG.MC_TRCMIN {45750} \
    CONFIG.MC_TRP {13750} \
    CONFIG.MC_TRPMIN {13750} \
    CONFIG.NUM_CLKS {8} \
    CONFIG.NUM_MC {1} \
    CONFIG.NUM_MCP {4} \
    CONFIG.NUM_MI {0} \
    CONFIG.NUM_SI {8} \
 ] $axi_noc_0
  #  CONFIG.CH0_DDR4_0_BOARD_INTERFACE {ddr4_dimm1} \
  #  CONFIG.sys_clk0_BOARD_INTERFACE {ddr4_dimm1_sma_clk} \

  set_property -dict [list CONFIG.CATEGORY {ps_cci} CONFIG.CONNECTIONS {MC_0 { read_bw {1720} write_bw {1720} read_avg_burst {4} write_avg_burst {4}}}] [get_bd_intf_pins /axi_noc_0/S00_AXI]
  set_property -dict [list CONFIG.CATEGORY {ps_cci} CONFIG.CONNECTIONS {MC_1 { read_bw {1720} write_bw {1720} read_avg_burst {4} write_avg_burst {4}}}] [get_bd_intf_pins /axi_noc_0/S01_AXI]
  set_property -dict [list CONFIG.CATEGORY {ps_cci} CONFIG.CONNECTIONS {MC_2 { read_bw {1720} write_bw {1720} read_avg_burst {4} write_avg_burst {4}}}] [get_bd_intf_pins /axi_noc_0/S02_AXI]
  set_property -dict [list CONFIG.CATEGORY {ps_cci} CONFIG.CONNECTIONS {MC_3 { read_bw {1720} write_bw {1720} read_avg_burst {4} write_avg_burst {4}}}] [get_bd_intf_pins /axi_noc_0/S03_AXI]
  set_property -dict [list CONFIG.CATEGORY {ps_rpu} CONFIG.CONNECTIONS {MC_0 { read_bw {1720} write_bw {1720} read_avg_burst {4} write_avg_burst {4}}}] [get_bd_intf_pins /axi_noc_0/S04_AXI]
  set_property -dict [list CONFIG.CATEGORY {ps_pmc} CONFIG.CONNECTIONS {MC_0 { read_bw {1720} write_bw {1720} read_avg_burst {4} write_avg_burst {4}}}] [get_bd_intf_pins /axi_noc_0/S05_AXI]
  set_property -dict [list CONFIG.CATEGORY {ps_nci} CONFIG.CONNECTIONS {MC_1 { read_bw {1720} write_bw {1720} read_avg_burst {4} write_avg_burst {4}}}] [get_bd_intf_pins /axi_noc_0/S06_AXI]
  set_property -dict [list CONFIG.CATEGORY {ps_nci} CONFIG.CONNECTIONS {MC_2 { read_bw {1720} write_bw {1720} read_avg_burst {4} write_avg_burst {4}}}] [get_bd_intf_pins /axi_noc_0/S07_AXI]
  #set_property -dict [list CONFIG.ASSOCIATED_BUSIF {S03_AXI:S02_AXI:S00_AXI:S01_AXI:S04_AXI:S07_AXI:S06_AXI:S05_AXI}] [get_bd_pins /axi_noc_0/aclk0]

  set_property -dict [ list \
   CONFIG.DATA_WIDTH {128} \
   CONFIG.REGION {0} \
   CONFIG.CONNECTIONS {MC_0 {read_bw {100} write_bw {100} read_avg_burst {4} write_avg_burst {4}}} \
   CONFIG.CATEGORY {ps_cci} \
 ] [get_bd_intf_pins /axi_noc_0/S00_AXI]

  set_property -dict [ list \
   CONFIG.DATA_WIDTH {128} \
   CONFIG.REGION {0} \
   CONFIG.CONNECTIONS {MC_1 {read_bw {100} write_bw {100} read_avg_burst {4} write_avg_burst {4}}} \
   CONFIG.CATEGORY {ps_cci} \
 ] [get_bd_intf_pins /axi_noc_0/S01_AXI]

  set_property -dict [ list \
   CONFIG.DATA_WIDTH {128} \
   CONFIG.REGION {0} \
   CONFIG.CONNECTIONS {MC_2 {read_bw {100} write_bw {100} read_avg_burst {4} write_avg_burst {4}}} \
   CONFIG.CATEGORY {ps_cci} \
 ] [get_bd_intf_pins /axi_noc_0/S02_AXI]

  set_property -dict [ list \
   CONFIG.DATA_WIDTH {128} \
   CONFIG.REGION {0} \
   CONFIG.CONNECTIONS {MC_3 {read_bw {100} write_bw {100} read_avg_burst {4} write_avg_burst {4}}} \
   CONFIG.CATEGORY {ps_cci} \
 ] [get_bd_intf_pins /axi_noc_0/S03_AXI]

  set_property -dict [ list \
   CONFIG.DATA_WIDTH {128} \
   CONFIG.REGION {0} \
   CONFIG.CONNECTIONS {MC_0 {read_bw {100} write_bw {100} read_avg_burst {4} write_avg_burst {4}}} \
   CONFIG.CATEGORY {ps_rpu} \
 ] [get_bd_intf_pins /axi_noc_0/S04_AXI]

  set_property -dict [ list \
   CONFIG.DATA_WIDTH {128} \
   CONFIG.REGION {0} \
   CONFIG.CONNECTIONS {MC_0 {read_bw {100} write_bw {100} read_avg_burst {4} write_avg_burst {4}}} \
   CONFIG.CATEGORY {ps_pmc} \
 ] [get_bd_intf_pins /axi_noc_0/S05_AXI]

  set_property -dict [ list \
   CONFIG.DATA_WIDTH {128} \
   CONFIG.CONNECTIONS {MC_1 { read_bw {1720} write_bw {1720} read_avg_burst {4} write_avg_burst {4}} } \
   CONFIG.CATEGORY {ps_nci} \
 ] [get_bd_intf_pins /axi_noc_0/S06_AXI]

  set_property -dict [ list \
   CONFIG.DATA_WIDTH {128} \
   CONFIG.CONNECTIONS {MC_2 { read_bw {1720} write_bw {1720} read_avg_burst {4} write_avg_burst {4}} } \
   CONFIG.CATEGORY {ps_nci} \
 ] [get_bd_intf_pins /axi_noc_0/S07_AXI]

  set_property -dict [ list \
   CONFIG.ASSOCIATED_BUSIF {S00_AXI} \
 ] [get_bd_pins /axi_noc_0/aclk0]

  set_property -dict [ list \
   CONFIG.ASSOCIATED_BUSIF {S01_AXI} \
 ] [get_bd_pins /axi_noc_0/aclk1]

  set_property -dict [ list \
   CONFIG.ASSOCIATED_BUSIF {S02_AXI} \
 ] [get_bd_pins /axi_noc_0/aclk2]

  set_property -dict [ list \
   CONFIG.ASSOCIATED_BUSIF {S03_AXI} \
 ] [get_bd_pins /axi_noc_0/aclk3]

  set_property -dict [ list \
   CONFIG.ASSOCIATED_BUSIF {S04_AXI} \
 ] [get_bd_pins /axi_noc_0/aclk4]

  set_property -dict [ list \
   CONFIG.ASSOCIATED_BUSIF {S05_AXI} \
 ] [get_bd_pins /axi_noc_0/aclk5]

  set_property -dict [ list \
   CONFIG.ASSOCIATED_BUSIF {S06_AXI} \
 ] [get_bd_pins /axi_noc_0/aclk6]

  set_property -dict [ list \
   CONFIG.ASSOCIATED_BUSIF {S07_AXI} \
 ] [get_bd_pins /axi_noc_0/aclk7]



  # Create variables to adapt between PS
  set ps_m_axi ps_0/M_AXI_FPD
  set ps_pl_clk ps_0/pl0_ref_clk
  set ps_axi_aclk ps_0/m_axi_fpd_aclk
  set ps_pl_resetn ps_0/pl0_resetn
  set ps_gpio_i ps_0/LPD_GPIO_i
  set ps_gpio_o ps_0/LPD_GPIO_o
  #connect_bd_intf_net -intf_net ps_0_M_AXI_FPD [get_bd_intf_pins ps_0/M_AXI_FPD] [get_bd_intf_pins PL/S00_AXI]

  # Connect DDR
  connect_bd_intf_net -intf_net axi_noc_0_CH0_DDR4_0 [get_bd_intf_ports ddr4_dimm1] [get_bd_intf_pins axi_noc_0/CH0_DDR4_0]
  connect_bd_intf_net -intf_net ddr4_dimm1_sma_clk_1 [get_bd_intf_ports ddr4_dimm1_sma_clk] [get_bd_intf_pins axi_noc_0/sys_clk0]
  # Connect axi_noc_0 to cips
  connect_bd_intf_net -intf_net ps_0_FPD_AXI_NOC_0 [get_bd_intf_pins axi_noc_0/S06_AXI] [get_bd_intf_pins ps_0/FPD_AXI_NOC_0]
  connect_bd_intf_net -intf_net ps_0_FPD_AXI_NOC_1 [get_bd_intf_pins axi_noc_0/S07_AXI] [get_bd_intf_pins ps_0/FPD_AXI_NOC_1]
  connect_bd_intf_net -intf_net ps_0_FPD_CCI_NOC_0 [get_bd_intf_pins axi_noc_0/S00_AXI] [get_bd_intf_pins ps_0/FPD_CCI_NOC_0]
  connect_bd_intf_net -intf_net ps_0_FPD_CCI_NOC_1 [get_bd_intf_pins axi_noc_0/S01_AXI] [get_bd_intf_pins ps_0/FPD_CCI_NOC_1]
  connect_bd_intf_net -intf_net ps_0_FPD_CCI_NOC_2 [get_bd_intf_pins axi_noc_0/S02_AXI] [get_bd_intf_pins ps_0/FPD_CCI_NOC_2]
  connect_bd_intf_net -intf_net ps_0_FPD_CCI_NOC_3 [get_bd_intf_pins axi_noc_0/S03_AXI] [get_bd_intf_pins ps_0/FPD_CCI_NOC_3]
  connect_bd_intf_net -intf_net ps_0_LPD_AXI_NOC_0 [get_bd_intf_pins axi_noc_0/S04_AXI] [get_bd_intf_pins ps_0/LPD_AXI_NOC_0]
  connect_bd_intf_net -intf_net ps_0_PMC_NOC_AXI_0 [get_bd_intf_pins axi_noc_0/S05_AXI] [get_bd_intf_pins ps_0/PMC_NOC_AXI_0]
  # axi_noc_0 clocks
  connect_bd_net [get_bd_pins axi_noc_0/aclk0] [get_bd_pins ps_0/fpd_cci_noc_axi0_clk]
  connect_bd_net [get_bd_pins axi_noc_0/aclk1] [get_bd_pins ps_0/fpd_cci_noc_axi1_clk]
  connect_bd_net [get_bd_pins axi_noc_0/aclk2] [get_bd_pins ps_0/fpd_cci_noc_axi2_clk]
  connect_bd_net [get_bd_pins axi_noc_0/aclk3] [get_bd_pins ps_0/fpd_cci_noc_axi3_clk]
  connect_bd_net [get_bd_pins axi_noc_0/aclk4] [get_bd_pins ps_0/lpd_axi_noc_clk]
  connect_bd_net [get_bd_pins axi_noc_0/aclk5] [get_bd_pins ps_0/pmc_axi_noc_axi0_clk]
  connect_bd_net [get_bd_pins axi_noc_0/aclk6] [get_bd_pins ps_0/fpd_axi_noc_axi0_clk]
  connect_bd_net [get_bd_pins axi_noc_0/aclk7] [get_bd_pins ps_0/fpd_axi_noc_axi1_clk]

  # Create XDC file with constraints
  set xdc_fd [ open $outputDir/jtag_constraints.xdc w ]
  puts $xdc_fd {create_clock -period 5000.000 -name {jtag_clk} -waveform {0.000 2500.000} [get_pins {caliptra_fpga_project_bd_i/ps_0/inst/pspmc_0/inst/PS9_inst/EMIOGPIO2O[0]}]}
  puts $xdc_fd {set_clock_groups -asynchronous -group [get_clocks {jtag_clk}]}
  close $xdc_fd
}

# Add AXI Interconnect
create_bd_cell -type ip -vlnv xilinx.com:ip:smartconnect:1.0 axi_interconnect_0
set_property -dict [list \
  CONFIG.NUM_MI {8} \
  CONFIG.NUM_SI {5} \
  CONFIG.NUM_CLKS {2} \
] [get_bd_cells axi_interconnect_0]
#set_property CONFIG.M03_SECURE {1} [get_bd_cells axi_interconnect_0]

if {$APB} {
  # Add AXI APB Bridge for Caliptra 1.x
  create_bd_cell -type ip -vlnv xilinx.com:ip:axi_apb_bridge:3.0 axi_apb_bridge_0
  set_property -dict [list \
    CONFIG.C_APB_NUM_SLAVES {1} \
    CONFIG.C_M_APB_PROTOCOL {apb4} \
  ] [get_bd_cells axi_apb_bridge_0]
  set_property location {3 1041 439} [get_bd_cells axi_apb_bridge_0]
}

# Add AXI BRAM Controller for backdoor access to IMEM
create_bd_cell -type ip -vlnv xilinx.com:ip:axi_bram_ctrl:4.1 axi_bram_ctrl_0
set_property CONFIG.SINGLE_PORT_BRAM {1} [get_bd_cells axi_bram_ctrl_0]

# Create reset block
create_bd_cell -type ip -vlnv xilinx.com:ip:proc_sys_reset:5.0 proc_sys_reset_0

save_bd_design
# TODO: Cleanup
# Add memory for SS
##create_bd_cell -type ip -vlnv xilinx.com:ip:blk_mem_gen:8.4 ss_imem_0
#create_bd_cell -type ip -vlnv xilinx.com:ip:axi_bram_ctrl:4.1 ss_imem_bram_ctrl_1
#set_property CONFIG.SINGLE_PORT_BRAM {1} [get_bd_cells ss_imem_bram_ctrl_1]
##connect_bd_intf_net [get_bd_intf_pins ss_imem_bram_ctrl_1/BRAM_PORTA] [get_bd_intf_pins ss_imem_0/BRAM_PORTA]
#connect_bd_net [get_bd_pins ss_imem_bram_ctrl_1/s_axi_aclk] [get_bd_pins $ps_pl_clk]
#connect_bd_net [get_bd_pins ss_imem_bram_ctrl_1/s_axi_aresetn] [get_bd_pins proc_sys_reset_0/peripheral_aresetn]
#connect_bd_intf_net [get_bd_intf_pins ss_imem_bram_ctrl_1/S_AXI] -boundary_type upper [get_bd_intf_pins axi_interconnect_0/M03_AXI]

# Move blocks around on the block diagram. This step is optional.
set_property location {1 177 345} [get_bd_cells ps_0]
set_property location {2 696 373} [get_bd_cells axi_interconnect_0]
set_property location {2 707 654} [get_bd_cells proc_sys_reset_0]
set_property location {3 1151 617} [get_bd_cells axi_bram_ctrl_0]
set_property location {4 1335 456} [get_bd_cells caliptra_package_top_0]

# AXI Managers to AXI Interconnect
# From the PS
connect_bd_intf_net [get_bd_intf_pins axi_interconnect_0/S00_AXI] [get_bd_intf_pins $ps_m_axi]
# Caliptra M_AXI
connect_bd_intf_net [get_bd_intf_pins axi_interconnect_0/S01_AXI] [get_bd_intf_pins caliptra_package_top_0/M_AXI_CALIPTRA]
# MCU
connect_bd_intf_net [get_bd_intf_pins caliptra_package_top_0/M_AXI_MCU_IFU] -boundary_type upper [get_bd_intf_pins axi_interconnect_0/S02_AXI]
connect_bd_intf_net [get_bd_intf_pins caliptra_package_top_0/M_AXI_MCU_LSU] -boundary_type upper [get_bd_intf_pins axi_interconnect_0/S03_AXI]
# MCI
connect_bd_intf_net [get_bd_intf_pins caliptra_package_top_0/M_AXI_MCI] -boundary_type upper [get_bd_intf_pins axi_interconnect_0/S04_AXI]

# AXI Interconnect to AXI Subordinates
# Caliptra
if {$APB} {
  connect_bd_intf_net [get_bd_intf_pins axi_interconnect_0/M00_AXI] [get_bd_intf_pins axi_apb_bridge_0/AXI4_LITE]
  connect_bd_intf_net [get_bd_intf_pins axi_apb_bridge_0/APB_M] [get_bd_intf_pins caliptra_package_top_0/s_apb]
} else {
  connect_bd_intf_net [get_bd_intf_pins axi_interconnect_0/M00_AXI] [get_bd_intf_pins caliptra_package_top_0/S_AXI_CALIPTRA]
}
# I3C
connect_bd_intf_net -boundary_type upper [get_bd_intf_pins axi_interconnect_0/M01_AXI] [get_bd_intf_pins caliptra_package_top_0/S_AXI_I3C]
# LCC
connect_bd_intf_net -boundary_type upper [get_bd_intf_pins axi_interconnect_0/M02_AXI] [get_bd_intf_pins caliptra_package_top_0/S_AXI_LCC]
# MCI
connect_bd_intf_net -boundary_type upper [get_bd_intf_pins axi_interconnect_0/M03_AXI] [get_bd_intf_pins caliptra_package_top_0/S_AXI_MCI]
# MCI ROM
connect_bd_intf_net -boundary_type upper [get_bd_intf_pins axi_interconnect_0/M04_AXI] [get_bd_intf_pins caliptra_package_top_0/S_AXI_MCI_ROM]
# OTP
connect_bd_intf_net -boundary_type upper [get_bd_intf_pins axi_interconnect_0/M05_AXI] [get_bd_intf_pins caliptra_package_top_0/S_AXI_OTP]
# Wrapper
connect_bd_intf_net [get_bd_intf_pins axi_interconnect_0/M06_AXI] [get_bd_intf_pins caliptra_package_top_0/S_AXI_WRAPPER]
# Caliptra ROM Backdoor
connect_bd_intf_net [get_bd_intf_pins axi_interconnect_0/M07_AXI] [get_bd_intf_pins axi_bram_ctrl_0/S_AXI]
connect_bd_intf_net [get_bd_intf_pins caliptra_package_top_0/axi_bram] [get_bd_intf_pins axi_bram_ctrl_0/BRAM_PORTA]

# Create reset connections
connect_bd_net [get_bd_pins $ps_pl_resetn] [get_bd_pins proc_sys_reset_0/ext_reset_in]
connect_bd_net -net proc_sys_reset_0_peripheral_aresetn \
  [get_bd_pins proc_sys_reset_0/peripheral_aresetn] \
  [get_bd_pins axi_apb_bridge_0/s_axi_aresetn] \
  [get_bd_pins axi_interconnect_0/aresetn] \
  [get_bd_pins caliptra_package_top_0/S_AXI_WRAPPER_ARESETN] \
  [get_bd_pins axi_bram_ctrl_0/s_axi_aresetn]
# Create clock connections
connect_bd_net \
  [get_bd_pins $ps_pl_clk] \
  [get_bd_pins $ps_axi_aclk] \
  [get_bd_pins proc_sys_reset_0/slowest_sync_clk] \
  [get_bd_pins axi_apb_bridge_0/s_axi_aclk] \
  [get_bd_pins axi_interconnect_0/aclk] \
  [get_bd_pins caliptra_package_top_0/core_clk] \
  [get_bd_pins axi_bram_ctrl_0/s_axi_aclk]
# Create clock connection for I3C
connect_bd_net \
  [get_bd_pins ps_0/pl1_ref_clk] \
  [get_bd_pins axi_interconnect_0/aclk1] \
  [get_bd_pins caliptra_package_top_0/i3c_clk]


# New connections for SS
#connect_bd_intf_net -boundary_type upper [get_bd_intf_pins axi_interconnect_0/M03_AXI] [get_bd_intf_pins caliptra_package_top_0/S_AXI_CALIPTRA]
#connect_bd_intf_net -boundary_type upper [get_bd_intf_pins axi_interconnect_0/M04_AXI] [get_bd_intf_pins caliptra_package_top_0/S_AXI_MCU_DMA]
#connect_bd_net [get_bd_pins proc_sys_reset_0/peripheral_aresetn] [get_bd_pins axi_interconnect_0/S01_ARESETN]
#connect_bd_net [get_bd_pins proc_sys_reset_0/peripheral_aresetn] [get_bd_pins axi_interconnect_0/S02_ARESETN]
#connect_bd_net [get_bd_pins proc_sys_reset_0/peripheral_aresetn] [get_bd_pins axi_interconnect_0/M03_ARESETN]
#connect_bd_net [get_bd_pins proc_sys_reset_0/peripheral_aresetn] [get_bd_pins axi_interconnect_0/M04_ARESETN]
#connect_bd_net [get_bd_pins ps_0/pl_clk0] [get_bd_pins axi_interconnect_0/S01_ACLK]
#connect_bd_net [get_bd_pins ps_0/pl_clk0] [get_bd_pins axi_interconnect_0/S02_ACLK]
#connect_bd_net [get_bd_pins ps_0/pl_clk0] [get_bd_pins axi_interconnect_0/M03_ACLK]
#connect_bd_net [get_bd_pins ps_0/pl_clk0] [get_bd_pins axi_interconnect_0/M04_ACLK]
# Connections for I3C
#connect_bd_net [get_bd_pins axi_interconnect_0/M06_ACLK] [get_bd_pins ps_0/pl_clk0]
#connect_bd_net [get_bd_pins axi_interconnect_0/M06_ARESETN] [get_bd_pins proc_sys_reset_0/peripheral_aresetn]

create_bd_port -dir O -type data SDA_UP
create_bd_port -dir O -type data SDA_PUSH
create_bd_port -dir O -type data SDA_PULL
create_bd_port -dir I -type data SDA
connect_bd_net [get_bd_pins /caliptra_package_top_0/SDA_UP]   [get_bd_ports SDA_UP]
connect_bd_net [get_bd_pins /caliptra_package_top_0/SDA_PUSH] [get_bd_ports SDA_PUSH]
connect_bd_net [get_bd_pins /caliptra_package_top_0/SDA_PULL] [get_bd_ports SDA_PULL]
connect_bd_net [get_bd_pins /caliptra_package_top_0/SDA]      [get_bd_ports SDA]

create_bd_port -dir O -type data SCL_UP
create_bd_port -dir O -type data SCL_PUSH
create_bd_port -dir O -type data SCL_PULL
create_bd_port -dir I -type data SCL
connect_bd_net [get_bd_pins /caliptra_package_top_0/SCL_UP]   [get_bd_ports SCL_UP]
connect_bd_net [get_bd_pins /caliptra_package_top_0/SCL_PUSH] [get_bd_ports SCL_PUSH]
connect_bd_net [get_bd_pins /caliptra_package_top_0/SCL_PULL] [get_bd_ports SCL_PULL]
connect_bd_net [get_bd_pins /caliptra_package_top_0/SCL]      [get_bd_ports SCL]

# Create address segments
if {$BOARD eq "ZCU104"} {
  set managers {ps_0/Data caliptra_package_top_0/M_AXI_MCU_IFU caliptra_package_top_0/M_AXI_MCU_LSU caliptra_package_top_0/M_AXI_CALIPTRA}
  foreach manager $managers {
    # Memories
    assign_bd_address -offset 0x80000000 -range 0x00020000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs axi_bram_ctrl_0/S_AXI/Mem0] -force
    assign_bd_address -offset 0x80020000 -range 0x00010000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_MCI_ROM/reg0] -force
    #assign_bd_address -offset 0x80020000 -range 0x00010000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs ss_imem_bram_ctrl_1/S_AXI/Mem0] -force
    # Wrapper
    assign_bd_address -offset 0x90010000 -range 0x00002000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_WRAPPER/reg0] -force
    # SS IPs
    assign_bd_address -offset 0x90030000 -range 0x00002000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_I3C/reg0] -force
    assign_bd_address -offset 0x90040000 -range 0x00002000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_LCC/reg0] -force
    assign_bd_address -offset 0x90050000 -range 0x00002000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_MCI/reg0] -force
    assign_bd_address -offset 0x90060000 -range 0x00002000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_OTP/reg0] -force
    # Caliptra Core
    if {$APB} {
      assign_bd_address -offset 0x90100000 -range 0x00100000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/s_apb/Reg] -force
    } else {
      assign_bd_address -offset 0x90100000 -range 0x00100000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_CALIPTRA/reg0] -force
    }
  }
} else {

  # DRAM
  assign_bd_address -offset 0x00000000 -range 0x80000000 -target_address_space [get_bd_addr_spaces ps_0/FPD_AXI_NOC_0] [get_bd_addr_segs axi_noc_0/S06_AXI/C1_DDR_LOW0] -force
  assign_bd_address -offset 0x000800000000 -range 0x000180000000 -target_address_space [get_bd_addr_spaces ps_0/FPD_AXI_NOC_0] [get_bd_addr_segs axi_noc_0/S06_AXI/C1_DDR_LOW1] -force
  assign_bd_address -offset 0x00000000 -range 0x80000000 -target_address_space [get_bd_addr_spaces ps_0/FPD_AXI_NOC_1] [get_bd_addr_segs axi_noc_0/S07_AXI/C2_DDR_LOW0] -force
  assign_bd_address -offset 0x000800000000 -range 0x000180000000 -target_address_space [get_bd_addr_spaces ps_0/FPD_AXI_NOC_1] [get_bd_addr_segs axi_noc_0/S07_AXI/C2_DDR_LOW1] -force
  assign_bd_address -offset 0x00000000 -range 0x80000000 -target_address_space [get_bd_addr_spaces ps_0/FPD_CCI_NOC_0] [get_bd_addr_segs axi_noc_0/S00_AXI/C0_DDR_LOW0] -force
  assign_bd_address -offset 0x000800000000 -range 0x000180000000 -target_address_space [get_bd_addr_spaces ps_0/FPD_CCI_NOC_0] [get_bd_addr_segs axi_noc_0/S00_AXI/C0_DDR_LOW1] -force
  assign_bd_address -offset 0x00000000 -range 0x80000000 -target_address_space [get_bd_addr_spaces ps_0/FPD_CCI_NOC_1] [get_bd_addr_segs axi_noc_0/S01_AXI/C1_DDR_LOW0] -force
  assign_bd_address -offset 0x000800000000 -range 0x000180000000 -target_address_space [get_bd_addr_spaces ps_0/FPD_CCI_NOC_1] [get_bd_addr_segs axi_noc_0/S01_AXI/C1_DDR_LOW1] -force
  assign_bd_address -offset 0x00000000 -range 0x80000000 -target_address_space [get_bd_addr_spaces ps_0/FPD_CCI_NOC_2] [get_bd_addr_segs axi_noc_0/S02_AXI/C2_DDR_LOW0] -force
  assign_bd_address -offset 0x000800000000 -range 0x000180000000 -target_address_space [get_bd_addr_spaces ps_0/FPD_CCI_NOC_2] [get_bd_addr_segs axi_noc_0/S02_AXI/C2_DDR_LOW1] -force
  assign_bd_address -offset 0x00000000 -range 0x80000000 -target_address_space [get_bd_addr_spaces ps_0/FPD_CCI_NOC_3] [get_bd_addr_segs axi_noc_0/S03_AXI/C3_DDR_LOW0] -force
  assign_bd_address -offset 0x000800000000 -range 0x000180000000 -target_address_space [get_bd_addr_spaces ps_0/FPD_CCI_NOC_3] [get_bd_addr_segs axi_noc_0/S03_AXI/C3_DDR_LOW1] -force
  assign_bd_address -offset 0x00000000 -range 0x80000000 -target_address_space [get_bd_addr_spaces ps_0/LPD_AXI_NOC_0] [get_bd_addr_segs axi_noc_0/S04_AXI/C0_DDR_LOW0] -force
  assign_bd_address -offset 0x000800000000 -range 0x000180000000 -target_address_space [get_bd_addr_spaces ps_0/LPD_AXI_NOC_0] [get_bd_addr_segs axi_noc_0/S04_AXI/C0_DDR_LOW1] -force

  assign_bd_address -offset 0x00000000 -range 0x80000000 -target_address_space [get_bd_addr_spaces ps_0/PMC_NOC_AXI_0] [get_bd_addr_segs axi_noc_0/S05_AXI/C0_DDR_LOW0] -force
  assign_bd_address -offset 0x000800000000 -range 0x000180000000 -target_address_space [get_bd_addr_spaces ps_0/PMC_NOC_AXI_0] [get_bd_addr_segs axi_noc_0/S05_AXI/C0_DDR_LOW1] -force

  # Caliptra register and memory interfaces
  set managers {get_bd_addr_spaces ps_0/M_AXI_FPD}
  # Other AXI managers
  set managers {ps_0/M_AXI_FPD caliptra_package_top_0/M_AXI_MCU_IFU caliptra_package_top_0/M_AXI_MCU_LSU caliptra_package_top_0/M_AXI_CALIPTRA caliptra_package_top_0/M_AXI_MCI}

  foreach manager $managers {
    # Memories
    assign_bd_address -offset 0xB0000000 -range 0x00018000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs axi_bram_ctrl_0/S_AXI/Mem0] -force
    assign_bd_address -offset 0xB0020000 -range 0x00010000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_MCI_ROM/reg0] -force
    #assign_bd_address -offset 0xB0020000 -range 0x00010000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs ss_imem_bram_ctrl_1/S_AXI/Mem0] -force
    # Wrapper
    assign_bd_address -offset 0xA4010000 -range 0x00002000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_WRAPPER/reg0] -force
    # SS IPs
    assign_bd_address -offset 0xA4030000 -range 0x00002000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_I3C/reg0] -force
    assign_bd_address -offset 0xA4040000 -range 0x00002000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_LCC/reg0] -force
    assign_bd_address -offset 0xA4050000 -range 0x00002000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_MCI/reg0] -force
    assign_bd_address -offset 0xA4060000 -range 0x00002000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_OTP/reg0] -force
    # Caliptra Core
    if {$APB} {
      assign_bd_address -offset 0xA4100000 -range 0x00100000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/s_apb/Reg] -force
    } else {
      assign_bd_address -offset 0xA4100000 -range 0x00100000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_CALIPTRA/reg0] -force
    }
  }

}

# Connect JTAG signals to PS GPIO pins
connect_bd_net [get_bd_pins caliptra_package_top_0/jtag_out] [get_bd_pins $ps_gpio_i]
connect_bd_net [get_bd_pins caliptra_package_top_0/jtag_in] [get_bd_pins $ps_gpio_o]

# Add constraints for JTAG signals
add_files -fileset constrs_1 $outputDir/jtag_constraints.xdc

# Caliptra SS connections
#connect_bd_net [get_bd_pins caliptra_package_top_0/S_AXI_WRAPPER_ARESETN] [get_bd_pins proc_sys_reset_0/peripheral_aresetn]
#connect_bd_intf_net [get_bd_intf_pins caliptra_package_top_0/S_AXI_WRAPPER] -boundary_type upper [get_bd_intf_pins axi_interconnect_0/M05_AXI]
#connect_bd_net [get_bd_pins axi_interconnect_0/M05_ACLK] [get_bd_pins ps_0/pl_clk0]
#connect_bd_net [get_bd_pins axi_interconnect_0/M05_ARESETN] [get_bd_pins proc_sys_reset_0/peripheral_aresetn]
#connect_bd_intf_net [get_bd_intf_pins ss_imem_bram_ctrl_1/BRAM_PORTA] [get_bd_intf_pins caliptra_package_top_0/ss_axi_bram]

save_bd_design
puts "Fileset when setting defines the second time: [current_fileset]"
set_property verilog_define $VERILOG_OPTIONS [current_fileset]
puts "\n\nVERILOG DEFINES: [get_property verilog_define [current_fileset]]"

# Create the HDL wrapper for the block design and add it. This will be set as top.
make_wrapper -files [get_files $outputDir/caliptra_fpga_project.srcs/sources_1/bd/caliptra_fpga_project_bd/caliptra_fpga_project_bd.bd] -top
add_files -norecurse $outputDir/caliptra_fpga_project.gen/sources_1/bd/caliptra_fpga_project_bd/hdl/caliptra_fpga_project_bd_wrapper.v
#add_files -norecurse  $fpgaDir/src/caliptra_fpga_project_bd_wrapper.v
set_property top caliptra_fpga_project_bd_wrapper [current_fileset]

update_compile_order -fileset sources_1

# Assign the gated clock conversion setting in the caliptra_package_top out of context run.
create_ip_run [get_files *caliptra_fpga_project_bd.bd]
set_property STEPS.SYNTH_DESIGN.ARGS.GATED_CLOCK_CONVERSION $GATED_CLOCK_CONVERSION [get_runs caliptra_fpga_project_bd_caliptra_package_top_0_0_synth_1]

# The FPGA loading methods currently in use require the bin file to be generated.
if {$BOARD eq "ZCU104"} {
  set_property STEPS.WRITE_BITSTREAM.ARGS.BIN_FILE true [get_runs impl_1]
} else {

  # Add DDR pin placement constraints
  add_files -fileset constrs_1 $fpgaDir/src/ddr4_constraints.xdc
}

# Start build
if {$BUILD} {
  launch_runs synth_1 -jobs 10
  wait_on_runs synth_1
  launch_runs impl_1 -jobs 10
  wait_on_runs impl_1
  open_run impl_1
  report_utilization -file $outputDir/utilization.txt
  # Embed git hash in USR_ACCESS register for bitstream identification.
  set_property BITSTREAM.CONFIG.USR_ACCESS 0x$VERSION [current_design]
  write_bitstream -bin_file $outputDir/caliptra_fpga
}

# TODO: Temp debug
if {$BOARD eq "ZCU104"} {
  set_property HDL_ATTRIBUTE.DEBUG true [get_bd_intf_nets {caliptra_ss_package_0_M_AXI_MCU_IFU caliptra_ss_package_0_M_AXI_MCU_LSU}]
  set_property HDL_ATTRIBUTE.DEBUG true [get_bd_intf_nets {axi_interconnect_0_M01_AXI}]
  set_property HDL_ATTRIBUTE.DEBUG true [get_bd_intf_nets {axi_interconnect_0_M03_AXI}]
  set_property HDL_ATTRIBUTE.DEBUG true [get_bd_intf_nets {ps_0_M_AXI_HPM0_LPD}]
  set_property HDL_ATTRIBUTE.DEBUG true [get_bd_intf_nets {axi_interconnect_0_M05_AXI}]
  set_property HDL_ATTRIBUTE.DEBUG true [get_bd_intf_nets {axi_interconnect_0_M06_AXI}]
  save_bd_design
}

# i3c_constraints.
#set_property IOSTANDARD LVCMOS33 [get_ports [list i3c_scl_io]]
#set_property IOSTANDARD LVCMOS33 [get_ports [list i3c_sda_io]]
#place_ports i3c_scl_io G8
#place_ports i3c_sda_io G7

# i3c constraints Versal
#place_ports i3c_scl_io BF24
#place_ports i3c_sda_io BC20
#set_property IOSTANDARD LVCMOS15 [get_ports [list i3c_scl_io]]
#set_property IOSTANDARD LVCMOS15 [get_ports [list i3c_sda_io]]

if {$BOARD eq "ZCU104"} {
  add_files -fileset constrs_1 $fpgaDir/src/zynq_i3c_constraints.xdc
} else {
  add_files -fileset constrs_1 $fpgaDir/src/versal_i3c_constraints.xdc
}
start_gui

# Consider constraint:
# set_max_delay -from [get_clocks clk_pl_0] -to [get_clocks clk_pl_1] 25.0
