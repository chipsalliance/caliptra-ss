OUTPUT_ARCH("riscv")
ENTRY(_start)
EXTERN(main)

SECTIONS {
  . = 0x50000000;
  .dccm : { *(.dccm) }
  __dccm_end = .;
  
  .data : { *(.data) *(.data.*) }
  __data_end = .;
  
  /* Only specific object files' rodata goes to DCCM - using your actual object files */
  .dccm.rodata : {
    /* List all available object files EXCEPT mci.o */
    mci_reg_rand_test.o(.rodata) mci_reg_rand_test.o(.rodata.*) mci_reg_rand_test.o(.srodata) mci_reg_rand_test.o(.srodata.*)
    printf.o(.rodata) printf.o(.rodata.*) printf.o(.srodata) printf.o(.srodata.*)
    caliptra_ss_lib.o(.rodata) caliptra_ss_lib.o(.rodata.*) caliptra_ss_lib.o(.srodata) caliptra_ss_lib.o(.srodata.*)
    fuse_ctrl.o(.rodata) fuse_ctrl.o(.rodata.*) fuse_ctrl.o(.srodata) fuse_ctrl.o(.srodata.*)
    lc_ctrl.o(.rodata) lc_ctrl.o(.rodata.*) lc_ctrl.o(.srodata) lc_ctrl.o(.srodata.*)
    mcu_crt0.o(.rodata) mcu_crt0.o(.rodata.*) mcu_crt0.o(.srodata) mcu_crt0.o(.srodata.*)
  }
  __dccm_rodata_end = .;
  
  .bss : { *(.bss) *(.sbss) *(.bss.*) *(.sbss.*) }
  __bss_end = .;
  
  STACK = ALIGN(16) + 0x1000;
  ASSERT((STACK < 0x50004000), "ERROR: Stack overflows the DCCM")
  
  . = 0x80000000;
  
  /* Create a separate section for _start that must come first in memory */
  .text.init : {
    mcu_crt0.o(.text.init)
  }
  
  /* Put mci_reg_rand_test.o with main() next */
  .text.main : {
    mci_reg_rand_test.o(.text.startup)
  }
  
  /* Then include the rest of the .text sections */
  .text : {
    /* Rest of mcu_crt0.o sections, excluding what's already placed */
    mcu_crt0.o(.text) mcu_crt0.o(.text.*)
    
    /* Rest of mci_reg_rand_test.o sections, excluding what's already placed */
    mci_reg_rand_test.o(.text) mci_reg_rand_test.o(.text.*)
    
    printf.o(.text*)
    caliptra_ss_lib.o(.text*)
    fuse_ctrl.o(.text*)
    lc_ctrl.o(.text*)
    mci.o(.text*)
    *(.text) *(.text.*)  /* Catch any others */
  }
  __text_end = .;
  
  /* Only mci.o's rodata goes to ROM */
  .rom.rodata : { 
    mci.o(.rodata) mci.o(.rodata.*) 
    mci.o(.srodata) mci.o(.srodata.*) 
  }
  __rom_rodata_end = .;
  
  ASSERT((__rom_rodata_end < 0x80010000), "ERROR: Program overflows ROM")
  
  . = 0x21000414;
  .data.io : { *(.data.io) }
}