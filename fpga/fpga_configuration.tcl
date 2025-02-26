
# Default settings:
set BUILD FALSE
set GUI   FALSE
set JTAG  TRUE
set ITRNG TRUE
set CG_EN FALSE
set RTL_VERSION latest
set BOARD VCK190
set DISABLE_ECC FALSE
set ENABLE_ADB TRUE
set ITRNG TRUE
set FAST_I3C FALSE

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
set outputDir $fpgaDir/caliptra_build
set caliptrapackageDir $outputDir/caliptra_package

# Clean and create output directory.
file delete -force $outputDir
file mkdir $outputDir
file mkdir $caliptrapackageDir

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

if {$BOARD eq "VCK190"} {
  set PART xcvc1902-vsva2197-2MP-e-S
  set BOARD_PART xilinx.com:vck190:part0:3.1
} elseif {$BOARD eq "VMK180"} {
  set PART xcvm1802-vsva2197-2MP-e-S
  set BOARD_PART xilinx.com:vmk180:part0:3.1
} else {
  puts "Board $BOARD not supported"
  exit
}

##### Caliptra Package #####
source create_caliptra_package.tcl
##### Caliptra Package #####


# Create a project for the SOC connections
create_project caliptra_fpga_project $outputDir -part $PART
set_property board_part $BOARD_PART [current_project]

# Include the packaged IP
set_property  ip_repo_paths "$caliptrapackageDir" [current_project]
update_ip_catalog

# Create SOC block design
create_bd_design "caliptra_fpga_project_bd"

# Add Caliptra package
create_bd_cell -type ip -vlnv design:user:caliptra_package_top:1.0 caliptra_package_top_0

# Add Versal PS
source create_versal_cips.tcl
# Connections to PS:
# set ps_m_axi ps_0/M_AXI_FPD
# set ps_pl_clk ps_0/pl0_ref_clk
# set ps_axi_aclk ps_0/m_axi_fpd_aclk
# set ps_pl_resetn ps_0/pl0_resetn
# set ps_gpio_i ps_0/LPD_GPIO_i
# set ps_gpio_o ps_0/LPD_GPIO_o

# Create XDC file with jtag constraints
set xdc_fd [ open $outputDir/jtag_constraints.xdc w ]
puts $xdc_fd {create_clock -period 5000.000 -name {jtag_clk} -waveform {0.000 2500.000} [get_pins {caliptra_fpga_project_bd_i/ps_0/inst/pspmc_0/inst/PS9_inst/EMIOGPIO2O[0]}]}
puts $xdc_fd {set_clock_groups -asynchronous -group [get_clocks {jtag_clk}]}
close $xdc_fd

# Add AXI Interconnect
create_bd_cell -type ip -vlnv xilinx.com:ip:smartconnect:1.0 axi_interconnect_0
set_property -dict [list \
  CONFIG.NUM_MI {10} \
  CONFIG.NUM_SI {5} \
  CONFIG.NUM_CLKS {2} \
] [get_bd_cells axi_interconnect_0]

if {$APB} {
  # Add AXI APB Bridge for Caliptra 1.x
  create_bd_cell -type ip -vlnv xilinx.com:ip:axi_apb_bridge:3.0 axi_apb_bridge_0
  set_property -dict [list \
    CONFIG.C_APB_NUM_SLAVES {1} \
    CONFIG.C_M_APB_PROTOCOL {apb4} \
  ] [get_bd_cells axi_apb_bridge_0]
  set_property location {3 1041 439} [get_bd_cells axi_apb_bridge_0]
}

# Add AXI BRAM Controller for backdoor access to Caliptra ROM
create_bd_cell -type ip -vlnv xilinx.com:ip:axi_bram_ctrl:4.1 cptra_rom_bram_ctrl_0
set_property CONFIG.SINGLE_PORT_BRAM {1} [get_bd_cells cptra_rom_bram_ctrl_0]

# Add AXI BRAM Controller for backdoor access to MCU ROM
create_bd_cell -type ip -vlnv xilinx.com:ip:axi_bram_ctrl:4.1 cptra_rom_bram_ctrl_1
set_property CONFIG.SINGLE_PORT_BRAM {1} [get_bd_cells cptra_rom_bram_ctrl_1]

# Create reset block
create_bd_cell -type ip -vlnv xilinx.com:ip:proc_sys_reset:5.0 proc_sys_reset_0

save_bd_design
# Add memory for MCU
create_bd_cell -type ip -vlnv xilinx.com:ip:axi_bram_ctrl:4.1 mcu_imem_bram_ctrl_1
set_property CONFIG.SINGLE_PORT_BRAM {1} [get_bd_cells mcu_imem_bram_ctrl_1]
connect_bd_net [get_bd_pins mcu_imem_bram_ctrl_1/s_axi_aclk] [get_bd_pins $ps_pl_clk]
connect_bd_net [get_bd_pins mcu_imem_bram_ctrl_1/s_axi_aresetn] [get_bd_pins proc_sys_reset_0/peripheral_aresetn]

create_bd_cell -type ip -vlnv xilinx.com:ip:emb_mem_gen:1.0 emb_mem_gen_0
set_property -dict [list \
  CONFIG.MEMORY_DEPTH {98304} \
  CONFIG.MEMORY_OPTIMIZATION {no_mem_opt} \
] [get_bd_cells emb_mem_gen_0]
connect_bd_intf_net [get_bd_intf_pins mcu_imem_bram_ctrl_1/BRAM_PORTA] [get_bd_intf_pins emb_mem_gen_0/BRAM_PORTA]
# Set regcea. Default should be 1
create_bd_cell -type ip -vlnv xilinx.com:ip:xlconstant:1.1 xlconstant_0
connect_bd_net [get_bd_pins xlconstant_0/dout] [get_bd_pins emb_mem_gen_0/regcea]

# Move blocks around on the block diagram. This step is optional.
set_property location {1 177 345} [get_bd_cells ps_0]
set_property location {2 696 373} [get_bd_cells axi_interconnect_0]
set_property location {2 707 654} [get_bd_cells proc_sys_reset_0]
set_property location {3 1151 617} [get_bd_cells cptra_rom_bram_ctrl_0]
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
connect_bd_intf_net -boundary_type upper [get_bd_intf_pins axi_interconnect_0/M04_AXI] [get_bd_intf_pins caliptra_package_top_0/S_AXI_MCU_ROM]
# OTP
connect_bd_intf_net -boundary_type upper [get_bd_intf_pins axi_interconnect_0/M05_AXI] [get_bd_intf_pins caliptra_package_top_0/S_AXI_OTP]
# Wrapper
connect_bd_intf_net -boundary_type upper [get_bd_intf_pins axi_interconnect_0/M06_AXI] [get_bd_intf_pins caliptra_package_top_0/S_AXI_WRAPPER]
# Caliptra ROM Backdoor
connect_bd_intf_net [get_bd_intf_pins axi_interconnect_0/M07_AXI] [get_bd_intf_pins cptra_rom_bram_ctrl_0/S_AXI]
connect_bd_intf_net [get_bd_intf_pins caliptra_package_top_0/rom_backdoor] [get_bd_intf_pins cptra_rom_bram_ctrl_0/BRAM_PORTA]
# MCU ROM Backdoor
connect_bd_intf_net [get_bd_intf_pins axi_interconnect_0/M08_AXI] [get_bd_intf_pins cptra_rom_bram_ctrl_1/S_AXI]
connect_bd_intf_net [get_bd_intf_pins caliptra_package_top_0/mcu_rom_backdoor] [get_bd_intf_pins cptra_rom_bram_ctrl_1/BRAM_PORTA]
# MCU RAM
connect_bd_intf_net -boundary_type upper [get_bd_intf_pins axi_interconnect_0/M09_AXI] [get_bd_intf_pins mcu_imem_bram_ctrl_1/S_AXI]

# Create reset connections
connect_bd_net [get_bd_pins $ps_pl_resetn] [get_bd_pins proc_sys_reset_0/ext_reset_in]
connect_bd_net -net proc_sys_reset_0_peripheral_aresetn \
  [get_bd_pins proc_sys_reset_0/peripheral_aresetn] \
  [get_bd_pins axi_apb_bridge_0/s_axi_aresetn] \
  [get_bd_pins axi_interconnect_0/aresetn] \
  [get_bd_pins caliptra_package_top_0/S_AXI_WRAPPER_ARESETN] \
  [get_bd_pins cptra_rom_bram_ctrl_0/s_axi_aresetn] \
  [get_bd_pins cptra_rom_bram_ctrl_1/s_axi_aresetn]
# Create clock connections
connect_bd_net \
  [get_bd_pins $ps_pl_clk] \
  [get_bd_pins $ps_axi_aclk] \
  [get_bd_pins proc_sys_reset_0/slowest_sync_clk] \
  [get_bd_pins axi_apb_bridge_0/s_axi_aclk] \
  [get_bd_pins axi_interconnect_0/aclk] \
  [get_bd_pins caliptra_package_top_0/core_clk] \
  [get_bd_pins cptra_rom_bram_ctrl_0/s_axi_aclk] \
  [get_bd_pins cptra_rom_bram_ctrl_1/s_axi_aclk]
# Create clock connection for I3C
if {$FAST_I3C} {
  # Use faster clock so that I3C bus speed is correct. TODO: Fails to meet timing
  connect_bd_net \
    [get_bd_pins ps_0/pl1_ref_clk] \
    [get_bd_pins axi_interconnect_0/aclk1] \
    [get_bd_pins caliptra_package_top_0/i3c_clk]
} else {
  # Use regular clock for i3c to avoid timing problems
  connect_bd_net \
    [get_bd_pins $ps_pl_clk] \
    [get_bd_pins axi_interconnect_0/aclk1] \
    [get_bd_pins caliptra_package_top_0/i3c_clk]
}

# Connections to I3C driver board
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

# Create address segments for all AXI managers
set managers {ps_0/M_AXI_FPD caliptra_package_top_0/M_AXI_MCU_IFU caliptra_package_top_0/M_AXI_MCU_LSU caliptra_package_top_0/M_AXI_CALIPTRA caliptra_package_top_0/M_AXI_MCI}

foreach manager $managers {
  # Memories
  assign_bd_address -offset 0xB0000000 -range 0x00018000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs cptra_rom_bram_ctrl_0/S_AXI/Mem0] -force
  assign_bd_address -offset 0xB0020000 -range 0x00020000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs cptra_rom_bram_ctrl_1/S_AXI/Mem0] -force
  assign_bd_address -offset 0xB0040000 -range 0x00020000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_MCU_ROM/reg0] -force
  assign_bd_address -offset 0xB0080000 -range 0x00080000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs mcu_imem_bram_ctrl_1/S_AXI/Mem0] -force
  # Wrapper
  assign_bd_address -offset 0xA4010000 -range 0x00002000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_WRAPPER/reg0] -force
  # SS IPs
  assign_bd_address -offset 0xA4030000 -range 0x00002000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_I3C/reg0] -force
  assign_bd_address -offset 0xA4040000 -range 0x00002000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_LCC/reg0] -force
  assign_bd_address -offset 0xA4060000 -range 0x00002000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_OTP/reg0] -force
  # Caliptra Core
  if {$APB} {
    assign_bd_address -offset 0xA4100000 -range 0x00100000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/s_apb/Reg] -force
  } else {
    assign_bd_address -offset 0xA4100000 -range 0x00100000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_CALIPTRA/reg0] -force
  }
  # MCI needs 0x200000. TODO: What is a reasonable size for this? MCU SRAM starts at 0x200000 so assume this needs extra.
  # TODO: integration spec has this take 0x0100_0000
  assign_bd_address -offset 0xA8000000 -range 0x01000000 -target_address_space [get_bd_addr_spaces $manager] [get_bd_addr_segs caliptra_package_top_0/S_AXI_MCI/reg0] -force
}

# Connect JTAG signals to PS GPIO pins
connect_bd_net [get_bd_pins caliptra_package_top_0/jtag_out] [get_bd_pins $ps_gpio_i]
connect_bd_net [get_bd_pins caliptra_package_top_0/jtag_in] [get_bd_pins $ps_gpio_o]

# Add constraints for JTAG signals
add_files -fileset constrs_1 $outputDir/jtag_constraints.xdc

save_bd_design
puts "Fileset when setting defines the second time: [current_fileset]"
set_property verilog_define $VERILOG_OPTIONS [current_fileset]
puts "\n\nVERILOG DEFINES: [get_property verilog_define [current_fileset]]"

# Create the HDL wrapper for the block design and add it. This will be set as top.
make_wrapper -files [get_files $outputDir/caliptra_fpga_project.srcs/sources_1/bd/caliptra_fpga_project_bd/caliptra_fpga_project_bd.bd] -top
add_files -norecurse $outputDir/caliptra_fpga_project.gen/sources_1/bd/caliptra_fpga_project_bd/hdl/caliptra_fpga_project_bd_wrapper.v
set_property top caliptra_fpga_project_bd_wrapper [current_fileset]

update_compile_order -fileset sources_1

# Assign the gated clock conversion setting in the caliptra_package_top out of context run.
create_ip_run [get_files *caliptra_fpga_project_bd.bd]
set_property STEPS.SYNTH_DESIGN.ARGS.GATED_CLOCK_CONVERSION $GATED_CLOCK_CONVERSION [get_runs caliptra_fpga_project_bd_caliptra_package_top_0_0_synth_1]

# Add DDR pin placement constraints
add_files -fileset constrs_1 $fpgaDir/src/ddr4_constraints.xdc

add_files -fileset constrs_1 $fpgaDir/src/versal_i3c_constraints.xdc

# Consider constraint:
# set_max_delay -from [get_clocks clk_pl_0] -to [get_clocks clk_pl_1] 25.0

# Start build
if {$BUILD} {
  launch_runs synth_1 -jobs 10
  wait_on_runs synth_1
  launch_runs impl_1 -to_step write_device_image -jobs 10
  wait_on_runs impl_1
  open_run impl_1
  report_utilization -file $outputDir/utilization.txt

  write_hw_platform -fixed -include_bit -force -file $outputDir/caliptra_fpga.xsa
}
