OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
    . = 0x80000000;
  .text   : { *(.text*) }
 _end = .;
  . = 0x80010000;
  .data  :  { *(.*data) *(.rodata*) *(.srodata*) *(.sbss) }
  .bss : { *(.bss) }
  STACK = ALIGN(16) + 0x1000;
  . = 0xd0580000;
  .data.io .  : { *(.data.io) }
}
