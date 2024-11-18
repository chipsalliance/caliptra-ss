## Create path variables
#set fpgaDir [file dirname [info script]]
#set outputDir $fpgaDir/caliptra_build
#set sspackageDir $outputDir/ss_package
#set adapterDir $outputDir/soc_adapter_package
## Clean and create output directory.
#file delete -force $outputDir
#file mkdir $outputDir
#file mkdir $sspackageDir
#file mkdir $adapterDir

set caliptrartlDir $fpgaDir/../third_party/caliptra-rtl
set ssrtlDir $fpgaDir/..

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
#lappend VERILOG_OPTIONS OUTSIDE
set_property verilog_define $VERILOG_OPTIONS [current_fileset]

#create_project soc_package_project $outputDir -part $PART
## Try setting after creating project
#set_property verilog_define $VERILOG_OPTIONS [current_fileset]

# Add ss RTL
#add_files [ glob $ssrtlDir/ ]
# Add MCU VEER Headers
#add_files $ssrtlDir/src/riscv_core/veer_el2/rtl/rev1p0/mcu_el2_param.vh
add_files $ssrtlDir/src/riscv_core/veer_el2/rtl/defines/pic_map_auto.h
add_files $ssrtlDir/src/riscv_core/veer_el2/rtl/defines/css_mcu0_el2_pdef.vh
add_files $ssrtlDir/src/riscv_core/veer_el2/rtl/defines/css_mcu0_common_defines.vh
add_files [ glob $ssrtlDir/src/riscv_core/veer_el2/rtl/design/include/*.svh ]
# Add MCU VEER sources
add_files [ glob $ssrtlDir/src/riscv_core/veer_el2/rtl/design/*.sv ]
add_files [ glob $ssrtlDir/src/riscv_core/veer_el2/rtl/design/*/*.sv ]
add_files [ glob $ssrtlDir/src/riscv_core/veer_el2/rtl/design/*/*.v ]

if {0} {
    # Add VEER Headers
    add_files $caliptrartlDir/src/riscv_core/veer_el2/rtl/el2_param.vh
    add_files $caliptrartlDir/src/riscv_core/veer_el2/rtl/pic_map_auto.h
    add_files $caliptrartlDir/src/riscv_core/veer_el2/rtl/el2_pdef.vh

    # Add VEER sources
    add_files [ glob $caliptrartlDir/src/riscv_core/veer_el2/rtl/*.sv ]
    add_files [ glob $caliptrartlDir/src/riscv_core/veer_el2/rtl/*/*.sv ]
    add_files [ glob $caliptrartlDir/src/riscv_core/veer_el2/rtl/*/*.v ]

    # Add Caliptra Headers (Weird how much requires the Caliptra RTL directory. Can this be excluded?)
    add_files [ glob $caliptrartlDir/src/*/rtl/*.svh ]
    # Add Caliptra Sources
    add_files [ glob $caliptrartlDir/src/*/rtl/*.sv ]
    add_files [ glob $caliptrartlDir/src/*/rtl/*.v ]
    # Trying this out. beh_lib.sv includes common_defines.sv
    # Follow-up: During packaging Vivado says that it may not be recognized as a synthesis include_dir after IP delivery
    #set_property include_dirs $caliptrartlDir/src/riscv_core/veer_el2/rtl [current_fileset]

    # Remove spi_host files that aren't used yet and are flagged as having syntax errors
    # TODO: Re-include these files when spi_host is used.
    remove_files [ glob $caliptrartlDir/src/spi_host/rtl/*.sv ]

    # Remove Caliptra files that need to be replaced by FPGA specific versions
    # Replace RAM with FPGA block ram
    #remove_files [ glob $caliptrartlDir/src/ecc/rtl/ecc_ram_tdp_file.sv ]
    # Key Vault is very large. Replacing KV with a version with the minimum number of entries.
    remove_files [ glob $caliptrartlDir/src/keyvault/rtl/kv_reg.sv ]

    # Remove ECDSA top
    remove_files [ glob $caliptrartlDir/src/ecc/rtl/ecc_top.sv ]
} else {
  # Attempting to add only the files needed by I3C
  add_files [ glob $caliptrartlDir/src/*/rtl/*.svh ]
  add_files [ glob $caliptrartlDir/src/caliptra_prim_generic/rtl/*.sv ]
  add_files [ glob $caliptrartlDir/src/caliptra_prim/rtl/*.sv ]
}

# I3C
set i3cDir $fpgaDir/../third_party/i3c-core
# Include headers and packages first
add_files [ glob $i3cDir/src/*.svh ]
add_files [ glob $i3cDir/src/*/*/*_pkg.sv ]
add_files [ glob $i3cDir/src/*/*_pkg.sv ]
add_files [ glob $i3cDir/src/*_pkg.sv ]
# Then the rest of the sv files
add_files [ glob $i3cDir/src/*/*/*.v ]
add_files [ glob $i3cDir/src/*/*/*.sv ]
add_files [ glob $i3cDir/src/*/*.sv ]
add_files [ glob $i3cDir/src/*.sv ]


# SS IPs
# TODO: changed from mcu to *
add_files [ glob $ssrtlDir/src/*/rtl/*.svh ]
add_files [ glob $ssrtlDir/src/*/rtl/*.sv ]

# Add FPGA specific sources
add_files [ glob $fpgaDir/src/*.sv]
add_files [ glob $fpgaDir/src/*.v]


if {0} {
  # Mark all Verilog sources as SystemVerilog because some of them have SystemVerilog syntax.
  set_property file_type SystemVerilog [get_files *.v]
  # Exception: caliptra_ss_package_top.v needs to be Verilog to be included in a Block Diagram.
  set_property file_type Verilog [get_files  $fpgaDir/src/caliptra_ss_package_top.v]

  set_property top caliptra_ss_package_top [current_fileset]

  ## Create block diagram that includes an instance of caliptra_package_top
  #create_bd_design "caliptra_ss_package_bd"
  #create_bd_cell -type module -reference caliptra_ss_package_top caliptra_ss_top_0
  #save_bd_design
  #close_bd_design [get_bd_designs caliptra_ss_package_bd]

  ipx::package_project -root_dir $sspackageDir -vendor design -library user -taxonomy /UserIP -import_files
  # Infer interfaces
  ipx::infer_bus_interfaces xilinx.com:interface:bram_rtl:1.0 [ipx::current_core]
  ipx::add_bus_parameter MASTER_TYPE [ipx::get_bus_interfaces ss_axi_bram -of_objects [ipx::current_core]]
  # Associate clocks to busses
  ipx::associate_bus_interfaces -busif ss_axi_bram -clock ss_axi_bram_clk [ipx::current_core]
  ipx::associate_bus_interfaces -busif M_AXI_MCU_IFU -clock core_clk [ipx::current_core]
  ipx::associate_bus_interfaces -busif M_AXI_MCU_LSU -clock core_clk [ipx::current_core]
  ipx::associate_bus_interfaces -busif S_AXI_MCU_DMA -clock core_clk [ipx::current_core]
  ipx::associate_bus_interfaces -busif sb_axi -clock core_clk [ipx::current_core]
  ipx::associate_bus_interfaces -busif S_AXI_WRAPPER -clock core_clk [ipx::current_core]
  ipx::associate_bus_interfaces -busif S_AXI_I3C -clock core_clk [ipx::current_core]
  # Other packager settings
  set_property PAYMENT_REQUIRED FALSE [ipx::current_core]
  ipx::update_source_project_archive -component [ipx::current_core]
  ipx::create_xgui_files [ipx::current_core]
  ipx::update_checksums [ipx::current_core]
  ipx::check_integrity [ipx::current_core]
  ipx::save_core [ipx::current_core]

  close_project
}