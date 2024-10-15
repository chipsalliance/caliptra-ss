OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  
  . = 0x50000000;
  .dccm : { *(.dccm) }
  _dccm_end = .;

  . = 0x80000000;
  .text   : { *(.text*) }
  _text_end = .;

  . = 0x80010000;
  .data  :  { *(.data*) }
  _data_end = .;

  . = 0x80011000;
  .bss : { *(.bss) }
  _bss_end = .;

  STACK = ALIGN(16) + 0x1000;
  
  . = 0xd0580000;
  .data.io : { *(.data.io) }
}