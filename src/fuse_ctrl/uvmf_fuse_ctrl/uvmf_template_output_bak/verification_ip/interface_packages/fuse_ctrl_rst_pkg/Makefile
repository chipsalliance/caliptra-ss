# fuse_ctrl_rst interface packages source
# pragma uvmf custom additional begin
# pragma uvmf custom additional end

fuse_ctrl_rst_PKG         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_rst_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_rst_pkg/fuse_ctrl_rst_filelist_hvl.f 

fuse_ctrl_rst_PKG_HDL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_rst_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_rst_pkg/fuse_ctrl_rst_filelist_hdl.f 

fuse_ctrl_rst_PKG_XRTL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_rst_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_rst_pkg/fuse_ctrl_rst_filelist_xrtl.f 

COMP_fuse_ctrl_rst_PKG_TGT_0 = q_comp_fuse_ctrl_rst_pkg
COMP_fuse_ctrl_rst_PKG_TGT_1 = v_comp_fuse_ctrl_rst_pkg
COMP_fuse_ctrl_rst_PKG_TGT = $(COMP_fuse_ctrl_rst_PKG_TGT_$(USE_VELOCE))

comp_fuse_ctrl_rst_pkg: $(COMP_fuse_ctrl_rst_PKG_TGT) 

q_comp_fuse_ctrl_rst_pkg:
	$(HDL_COMP_CMD) $(fuse_ctrl_rst_PKG_HDL)
	$(HVL_COMP_CMD) $(fuse_ctrl_rst_PKG)
	$(HDL_COMP_CMD) $(fuse_ctrl_rst_PKG_XRTL) 

v_comp_fuse_ctrl_rst_pkg:
	$(HVL_COMP_CMD) $(fuse_ctrl_rst_PKG_HDL)
	$(HVL_COMP_CMD) $(fuse_ctrl_rst_PKG)
	$(VELANALYZE_CMD) $(fuse_ctrl_rst_PKG_HDL) 
	$(VELANALYZE_HVL_CMD) $(fuse_ctrl_rst_PKG) 
	$(HDL_COMP_CMD) $(fuse_ctrl_rst_PKG_XRTL)

ifeq ($(MTI_VCO_MODE),64)
  GCC_COMP_ARCH = -m64
else
  GCC_COMP_ARCH = -m32
endif

export fuse_ctrl_rst_IF_DPI_SRC ?= $(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_rst_pkg/dpi

C_FILE_COMPILE_LIST_fuse_ctrl_rst_pkg	= \

O_FILE_COMPILE_LIST_fuse_ctrl_rst_pkg = $(notdir $(C_FILE_COMPILE_LIST_fuse_ctrl_rst_pkg:.c=.o))

GCC_COMP_ARGS_fuse_ctrl_rst_pkg	+= -I$(fuse_ctrl_rst_IF_DPI_SRC) \
	-fPIC 

GCC_COMP_ARGS_fuse_ctrl_rst_pkg	+= $(fuse_ctrl_rst_IF_GCC_COMP_ARGUMENTS)

GCC_LINK_ARGS_fuse_ctrl_rst_pkg	+= \
	 \
 	-o .so

comp_fuse_ctrl_rst_pkg_c_files:
	@echo "--------------------------------"
	@echo "Compiling Interface C source"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_COMP_ARGS_fuse_ctrl_rst_pkg) $(C_FILE_COMPILE_LIST_fuse_ctrl_rst_pkg)
	@echo "--------------------------------"
	@echo "Linking Interface C objects into a shared object"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_LINK_ARGS_fuse_ctrl_rst_pkg) $(O_FILE_COMPILE_LIST_fuse_ctrl_rst_pkg)
	@echo "--------------------------------"

