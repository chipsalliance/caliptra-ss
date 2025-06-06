

##################################################################
## ENVIRONMENT VARIABLES
##################################################################
quietly set ::env(UVMF_VIP_LIBRARY_HOME) ../../../verification_ip
quietly set ::env(UVMF_PROJECT_DIR) ..

## Using VRM means that the build is occuring several more directories deeper underneath
## the sim directory, need to prepend some more '..'
if {[info exists ::env(VRM_BUILD)]} {
  quietly set ::env(UVMF_VIP_LIBRARY_HOME) "../../../../../$::env(UVMF_VIP_LIBRARY_HOME)"
  quietly set ::env(UVMF_PROJECT_DIR) "../../../../../$::env(UVMF_PROJECT_DIR)"
}
quietly set ::env(UVMF_VIP_LIBRARY_HOME) [file normalize $::env(UVMF_VIP_LIBRARY_HOME)]
quietly set ::env(UVMF_PROJECT_DIR) [file normalize $::env(UVMF_PROJECT_DIR)]
quietly echo "UVMF_VIP_LIBRARY_HOME = $::env(UVMF_VIP_LIBRARY_HOME)"
quietly echo "UVMF_PROJECT_DIR = $::env(UVMF_PROJECT_DIR)"


###################################################################
## HOUSEKEEPING : DELETE FILES THAT WILL BE REGENERATED
###################################################################
file delete -force *~ *.ucdb vsim.dbg *.vstf *.log work *.mem *.transcript.txt certe_dump.xml *.wlf covhtmlreport VRMDATA
file delete -force design.bin qwave.db dpiheader.h visualizer*.ses
file delete -force veloce.med veloce.wave veloce.map tbxbindings.h edsenv velrunopts.ini
file delete -force sv_connect.*

###################################################################
## COMPILE DUT SOURCE CODE
###################################################################
vlib work 
# pragma uvmf custom dut_compile_dofile_target begin
# UVMF_CHANGE_ME : Add commands to compile your dut here, replacing the default examples
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/rtl/verilog/verilog_dut.v
vcom $env(UVMF_PROJECT_DIR)/rtl/vhdl/vhdl_dut.vhd
# pragma uvmf custom dut_compile_dofile_target end

###################################################################
## COMPILE UVMF BASE/COMMON SOURCE CODE
###################################################################
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_HOME)/uvmf_base_pkg -F $env(UVMF_HOME)/uvmf_base_pkg/uvmf_base_pkg_filelist_hdl.f
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_HOME)/uvmf_base_pkg -F $env(UVMF_HOME)/uvmf_base_pkg/uvmf_base_pkg_filelist_hvl.f


###################################################################
## UVMF INTERFACE COMPILATION
###################################################################
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_rst_in_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_rst_out_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_core_axi_write_in_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_core_axi_write_out_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_prim_axi_write_in_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_prim_axi_write_out_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_core_axi_read_in_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_core_axi_read_out_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_prim_axi_read_in_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_prim_axi_read_out_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_secreg_axi_read_in_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_secreg_axi_read_out_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_lc_otp_in_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_lc_otp_out_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_in_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_out_pkg/compile.do

###################################################################
## UVMF ENVIRONMENT COMPILATION
###################################################################
do $env(UVMF_VIP_LIBRARY_HOME)/environment_packages/fuse_ctrl_env_pkg/compile.do

###################################################################
## UVMF BENCHES COMPILATION
###################################################################
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_PROJECT_DIR)/tb/parameters $env(UVMF_PROJECT_DIR)/tb/parameters/fuse_ctrl_parameters_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_PROJECT_DIR)/tb/sequences $env(UVMF_PROJECT_DIR)/tb/sequences/fuse_ctrl_sequences_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_PROJECT_DIR)/tb/tests $env(UVMF_PROJECT_DIR)/tb/tests/fuse_ctrl_tests_pkg.sv

vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_PROJECT_DIR)/tb/testbench -F $env(UVMF_PROJECT_DIR)/tb/testbench/top_filelist_hdl.f
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286  +incdir+$env(UVMF_PROJECT_DIR)/tb/testbench -F $env(UVMF_PROJECT_DIR)/tb/testbench/top_filelist_hvl.f

###################################################################
## OPTIMIZATION
###################################################################
vopt          hvl_top hdl_top   -o optimized_batch_top_tb
vopt  +acc    hvl_top hdl_top   -o optimized_debug_top_tb
