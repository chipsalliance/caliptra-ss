
# Create a project to package Caliptra.
# Packaging Caliptra allows Vivado to recognize the APB bus as an endpoint for the memory map.
create_project caliptra_package_project $outputDir -part $PART
if {$BOARD eq "VCK190"} {
  set_property board_part xilinx.com:vck190:part0:3.1 [current_project]
}

# TODO: Check these SS defines
lappend VERILOG_OPTIONS TECH_SPECIFIC_ICG
lappend VERILOG_OPTIONS USER_ICG=fpga_fake_icg
lappend VERILOG_OPTIONS RV_FPGA_OPTIMIZE
lappend VERILOG_OPTIONS css_mcu0_TEC_RV_ICG=css_mcu0_clockhdr
lappend VERILOG_OPTIONS TECH_SPECIFIC_EC_RV_ICG
lappend VERILOG_OPTIONS css_mcu0_USER_EC_RV_ICG=mcu_clockhdr
lappend VERILOG_OPTIONS css_mcu0_RV_BUILD_AXI4
lappend VERILOG_OPTIONS MCU_RV_BUILD_AXI4
lappend VERILOG_OPTIONS I3C_USE_AXI
# TODO: This AXI_ID_WIDTH is probably way larger than needed.
lappend VERILOG_OPTIONS AXI_ID_WIDTH=19 AXI_USER_WIDTH=32 AXI_DATA_WIDTH=32 AXI_ADDR_WIDTH=32
# Might be removed in newer RTL? TLUL has compilation failure
lappend VERILOG_OPTIONS CALIPTRA_AXI_ID_WIDTH=19 CALIPTRA_AXI_USER_WIDTH=32

set_property verilog_define $VERILOG_OPTIONS [current_fileset]
puts "\n\nVERILOG DEFINES: [get_property verilog_define [current_fileset]]"

# Add Caliptra VEER Headers
add_files $caliptrartlDir/src/riscv_core/veer_el2/rtl/el2_param.vh
add_files $caliptrartlDir/src/riscv_core/veer_el2/rtl/pic_map_auto.h
add_files $caliptrartlDir/src/riscv_core/veer_el2/rtl/el2_pdef.vh
add_files [ glob $caliptrartlDir/src/riscv_core/veer_el2/rtl/include/*.svh ]
add_files [ glob $caliptrartlDir/src/riscv_core/veer_el2/rtl/include/*.sv ]

# Add Caliptra VEER sources
add_files [ glob $caliptrartlDir/src/riscv_core/veer_el2/rtl/*.sv ]
add_files [ glob $caliptrartlDir/src/riscv_core/veer_el2/rtl/*/*.sv ]
add_files [ glob $caliptrartlDir/src/riscv_core/veer_el2/rtl/*/*.v ]

# Add Adam's Bridge
if {$ENABLE_ADB} {
  source adams-bridge-files.tcl
}
# Add Caliptra headers and packages
add_files [ glob $caliptrartlDir/src/*/rtl/*.svh ]
add_files [ glob $caliptrartlDir/src/*/rtl/*_pkg.sv ]
# Add Caliptra sources
add_files [ glob $caliptrartlDir/src/*/rtl/*.sv ]
add_files [ glob $caliptrartlDir/src/*/rtl/*.v ]

# Add ss RTL
# Add MCU VEER Headers
add_files $ssrtlDir/src/riscv_core/veer_el2/rtl/defines/pic_map_auto.h
add_files $ssrtlDir/src/riscv_core/veer_el2/rtl/defines/css_mcu0_el2_pdef.vh
add_files $ssrtlDir/src/riscv_core/veer_el2/rtl/defines/css_mcu0_el2_param.vh
add_files $ssrtlDir/src/riscv_core/veer_el2/rtl/defines/css_mcu0_common_defines.vh
add_files [ glob $ssrtlDir/src/riscv_core/veer_el2/rtl/design/include/*.svh ]
# For SS EL2_IC_DATA_SRAM is defined in testbench
add_files [ glob $ssrtlDir/src/riscv_core/veer_el2/tb/icache_macros.svh ]
# Add MCU VEER sources
add_files [ glob $ssrtlDir/src/riscv_core/veer_el2/rtl/design/*.sv ]
add_files [ glob $ssrtlDir/src/riscv_core/veer_el2/rtl/design/*/*.sv ]
add_files [ glob $ssrtlDir/src/riscv_core/veer_el2/rtl/design/*/*.v ]
# OTP
add_files [ glob $ssrtlDir/src/fuse_ctrl/rtl/*.sv ]
# OTP memory
add_files $ssrtlDir/src/fuse_ctrl/data/otp-img.2048.vmem
set_property file_type {Memory Initialization Files} [get_files $ssrtlDir/src/fuse_ctrl/data/otp-img.2048.vmem]
# OTP from testbench
add_files $ssrtlDir/src/integration/testbench/prim_generic_otp.sv
# MCU VEER sram from testbench
add_files $ssrtlDir/src/integration/testbench/caliptra_ss_veer_sram_export.sv
# SS IPs
add_files [ glob $ssrtlDir/src/*/rtl/*.svh ]
add_files [ glob $ssrtlDir/src/*/rtl/*.sv ]

# I3C
set i3cDir $fpgaDir/../third_party/i3c-core
# Include headers and packages first
add_files [ glob $i3cDir/src/*.svh ]
add_files [ glob $i3cDir/src/libs/*.svh ]
add_files [ glob $i3cDir/src/*/*/*_pkg.sv ]
add_files [ glob $i3cDir/src/*/*_pkg.sv ]
add_files [ glob $i3cDir/src/*_pkg.sv ]
# Then the rest of the sv files
#add_files [ glob $i3cDir/src/*/*/*.v ]
add_files [ glob $i3cDir/src/*/*/*.sv ]
add_files [ glob $i3cDir/src/*/*.sv ]
add_files [ glob $i3cDir/src/*.sv ]
# Remove the i3c-core versions of the AXI modules, so that it uses the caliptra-rtl versions instead
#remove_files [ glob $i3cDir/src/libs/*.svh ]
#remove_files [ glob $i3cDir/src/libs/axi_sub/*.sv ]

# Remove spi_host files that aren't used yet and are flagged as having syntax errors
# TODO: Re-include these files when spi_host is used.
remove_files [ glob $caliptrartlDir/src/spi_host/rtl/*.sv ]

# Remove Caliptra files that need to be replaced by FPGA specific versions
# Key Vault is very large. Replacing KV with a version with the minimum number of entries.
#remove_files [ glob $caliptrartlDir/src/keyvault/rtl/kv_reg.sv ]

# Add FPGA specific sources
add_files [ glob $fpgaDir/src/*.sv]
add_files [ glob $fpgaDir/src/*.v]


if {$DISABLE_ECC} {
  # Remove ECC to be replaced by stub for SS
  remove_files [ glob $caliptrartlDir/src/ecc/rtl/*.sv ]
} else {
  # Replace RAM with FPGA block ram
  remove_files [ glob $caliptrartlDir/src/ecc/rtl/ecc_ram_tdp_file.sv ]
  # Remove ECC stub from FPGA files
  remove_files $fpgaDir/src/ecc_stub.sv
}

if {$ENABLE_ADB} {
  # Remove MLDSA stub
  remove_files $fpgaDir/src/mldsa_stub.sv
}

# TODO: Copy aes_clk_wrapper.sv to apply workaround
file copy [ glob $caliptrartlDir/src/aes/rtl/aes_clp_wrapper.sv ] $outputDir/aes_clk_wrapper.sv
exec sed -i {1i `include \"kv_macros.svh\"} $outputDir/aes_clk_wrapper.sv
remove_files [ glob $caliptrartlDir/src/aes/rtl/aes_clp_wrapper.sv ]
add_files $outputDir/aes_clk_wrapper.sv

# Mark all Verilog sources as SystemVerilog because some of them have SystemVerilog syntax.
set_property file_type SystemVerilog [get_files *.v]

# Exception: caliptra_package_top.v needs to be Verilog to be included in a Block Diagram.
set_property file_type Verilog [get_files  $fpgaDir/src/caliptra_package_top.v]

# Add include paths
set_property include_dirs $caliptrartlDir/src/integration/rtl [current_fileset]


# Set caliptra_package_top as top in case next steps fail so that the top is something useful.
if {$APB} {
  set_property top caliptra_package_apb_top [current_fileset]
} else {
  set_property top caliptra_package_axi_top [current_fileset]
}

# Create block diagram that includes an instance of caliptra_package_top
create_bd_design "caliptra_package_bd"
if {$APB} {
  create_bd_cell -type module -reference caliptra_package_apb_top caliptra_package_top_0
} else {
  create_bd_cell -type module -reference caliptra_package_axi_top caliptra_package_top_0
}
save_bd_design
close_bd_design [get_bd_designs caliptra_package_bd]

# Package IP
puts "Fileset when packaging: [current_fileset]"
puts "\n\nVERILOG DEFINES: [get_property verilog_define [current_fileset]]"
ipx::package_project -root_dir $caliptrapackageDir -vendor design -library user -taxonomy /UserIP -import_files
# Infer interfaces
ipx::infer_bus_interfaces xilinx.com:interface:apb_rtl:1.0 [ipx::current_core]
ipx::infer_bus_interfaces xilinx.com:interface:bram_rtl:1.0 [ipx::current_core]
ipx::add_bus_parameter MASTER_TYPE [ipx::get_bus_interfaces rom_backdoor -of_objects [ipx::current_core]]
ipx::add_bus_parameter MASTER_TYPE [ipx::get_bus_interfaces mcu_rom_backdoor -of_objects [ipx::current_core]]
ipx::add_bus_parameter MASTER_TYPE [ipx::get_bus_interfaces otp_mem_backdoor -of_objects [ipx::current_core]]
# Associate clocks to busses
ipx::associate_bus_interfaces -busif S_AXI_WRAPPER -clock core_clk [ipx::current_core]
ipx::associate_bus_interfaces -busif S_AXI_CALIPTRA -clock core_clk [ipx::current_core]
ipx::associate_bus_interfaces -busif M_AXI_CALIPTRA -clock core_clk [ipx::current_core]
ipx::associate_bus_interfaces -busif rom_backdoor -clock rom_backdoor_clk [ipx::current_core]
ipx::associate_bus_interfaces -busif mcu_rom_backdoor -clock mcu_rom_backdoor_clk [ipx::current_core]
ipx::associate_bus_interfaces -busif otp_mem_backdoor -clock otp_mem_backdoor_clk [ipx::current_core]

ipx::associate_bus_interfaces -busif M_AXI_MCU_IFU -clock core_clk [ipx::current_core]
ipx::associate_bus_interfaces -busif M_AXI_MCU_LSU -clock core_clk [ipx::current_core]
ipx::associate_bus_interfaces -busif M_AXI_MCU_SB -clock core_clk [ipx::current_core]
ipx::associate_bus_interfaces -busif S_AXI_MCI -clock core_clk [ipx::current_core]
ipx::associate_bus_interfaces -busif S_AXI_MCU_ROM -clock core_clk [ipx::current_core]
ipx::associate_bus_interfaces -busif S_AXI_OTP -clock core_clk [ipx::current_core]
ipx::associate_bus_interfaces -busif S_AXI_LCC -clock core_clk [ipx::current_core]
# Different clock used for I3C
ipx::associate_bus_interfaces -busif S_AXI_I3C -clock i3c_clk [ipx::current_core]

# Other packager settings
set_property name caliptra_package_top [ipx::current_core]
set_property core_revision 1 [ipx::current_core]
set_property PAYMENT_REQUIRED FALSE [ipx::current_core]
ipx::update_source_project_archive -component [ipx::current_core]
ipx::create_xgui_files [ipx::current_core]
ipx::update_checksums [ipx::current_core]
ipx::check_integrity [ipx::current_core]
ipx::save_core [ipx::current_core]

# Close caliptra_package_project
close_project
