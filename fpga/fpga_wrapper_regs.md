<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: caliptra_fpga_realtime_regs
  - caliptra_fpga_realtime_regs.rdl
-->

## caliptra_fpga_realtime_regs address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x101C

|Offset|  Identifier  |Name|
|------|--------------|----|
|0x0000|interface_regs|  — |
|0x1000|   fifo_regs  |  — |

## interface_regs register file

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x78

|Offset|         Identifier        |Name|
|------|---------------------------|----|
| 0x00 |   generic_input_wires[0]  |  — |
| 0x04 |   generic_input_wires[1]  |  — |
| 0x08 |  generic_output_wires[0]  |  — |
| 0x0C |  generic_output_wires[1]  |  — |
| 0x10 |      cptra_obf_key[0]     |  — |
| 0x14 |      cptra_obf_key[1]     |  — |
| 0x18 |      cptra_obf_key[2]     |  — |
| 0x1C |      cptra_obf_key[3]     |  — |
| 0x20 |      cptra_obf_key[4]     |  — |
| 0x24 |      cptra_obf_key[5]     |  — |
| 0x28 |      cptra_obf_key[6]     |  — |
| 0x2C |      cptra_obf_key[7]     |  — |
| 0x30 |          control          |  — |
| 0x34 |           status          |  — |
| 0x38 |           pauser          |  — |
| 0x3C |       itrng_divisor       |  — |
| 0x40 |        cycle_count        |  — |
| 0x44 |        fpga_version       |  — |
| 0x48 |          lsu_user         |  — |
| 0x4C |          ifu_user         |  — |
| 0x50 |          clp_user         |  — |
| 0x54 |      soc_config_user      |  — |
| 0x58 |      sram_config_user     |  — |
| 0x5C |      mcu_reset_vector     |  — |
| 0x60 |         mci_error         |  — |
| 0x64 |         mcu_config        |  — |
| 0x68 | mci_generic_input_wires[0]|  — |
| 0x6C | mci_generic_input_wires[1]|  — |
| 0x70 |mci_generic_output_wires[0]|  — |
| 0x74 |mci_generic_output_wires[1]|  — |

### generic_input_wires register

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### generic_input_wires register

- Absolute Address: 0x4
- Base Offset: 0x0
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### generic_output_wires register

- Absolute Address: 0x8
- Base Offset: 0x8
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |   r  | 0x0 |  — |

### generic_output_wires register

- Absolute Address: 0xC
- Base Offset: 0x8
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |   r  | 0x0 |  — |

### cptra_obf_key register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_key register

- Absolute Address: 0x14
- Base Offset: 0x10
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_key register

- Absolute Address: 0x18
- Base Offset: 0x10
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_key register

- Absolute Address: 0x1C
- Base Offset: 0x10
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_key register

- Absolute Address: 0x20
- Base Offset: 0x10
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_key register

- Absolute Address: 0x24
- Base Offset: 0x10
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_key register

- Absolute Address: 0x28
- Base Offset: 0x10
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_key register

- Absolute Address: 0x2C
- Base Offset: 0x10
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### control register

- Absolute Address: 0x30
- Base Offset: 0x30
- Size: 0x4

|Bits|   Identifier   |Access|Reset|Name|
|----|----------------|------|-----|----|
|  0 |  cptra_pwrgood |  rw  | 0x0 |  — |
|  1 | cptra_ss_rst_b |  rw  | 0x0 |  — |
|  2 |bootfsm_brkpoint|  rw  | 0x0 |  — |

### status register

- Absolute Address: 0x34
- Base Offset: 0x34
- Size: 0x4

|Bits|      Identifier     |Access|Reset|Name|
|----|---------------------|------|-----|----|
|  0 |  cptra_error_fatal  |   r  | 0x0 |  — |
|  1 |cptra_error_non_fatal|   r  | 0x0 |  — |
|  2 |   ready_for_fuses   |   r  | 0x0 |  — |
|  3 |  ready_for_fw_push  |   r  | 0x0 |  — |
|  4 |  ready_for_runtime  |   r  | 0x0 |  — |
|  5 |  mailbox_data_avail |   r  | 0x0 |  — |
|  6 |  mailbox_flow_done  |   r  | 0x0 |  — |

### pauser register

- Absolute Address: 0x38
- Base Offset: 0x38
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|  pauser  |  rw  | 0x0 |  — |

### itrng_divisor register

- Absolute Address: 0x3C
- Base Offset: 0x3C
- Size: 0x4

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|itrng_divisor|  rw  | 0x0 |  — |

### cycle_count register

- Absolute Address: 0x40
- Base Offset: 0x40
- Size: 0x4

|Bits| Identifier|Access|Reset|Name|
|----|-----------|------|-----|----|
|31:0|cycle_count|   r  | 0x0 |  — |

### fpga_version register

- Absolute Address: 0x44
- Base Offset: 0x44
- Size: 0x4

|Bits| Identifier |Access|Reset|Name|
|----|------------|------|-----|----|
|31:0|fpga_version|   r  | 0x0 |  — |

### lsu_user register

- Absolute Address: 0x48
- Base Offset: 0x48
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0| lsu_user |  rw  | 0x0 |  — |

### ifu_user register

- Absolute Address: 0x4C
- Base Offset: 0x4C
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0| ifu_user |  rw  | 0x0 |  — |

### clp_user register

- Absolute Address: 0x50
- Base Offset: 0x50
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0| clp_user |  rw  | 0x0 |  — |

### soc_config_user register

- Absolute Address: 0x54
- Base Offset: 0x54
- Size: 0x4

|Bits|   Identifier  |Access|Reset|Name|
|----|---------------|------|-----|----|
|31:0|soc_config_user|  rw  | 0x0 |  — |

### sram_config_user register

- Absolute Address: 0x58
- Base Offset: 0x58
- Size: 0x4

|Bits|   Identifier   |Access|Reset|Name|
|----|----------------|------|-----|----|
|31:0|sram_config_user|  rw  | 0x0 |  — |

### mcu_reset_vector register

- Absolute Address: 0x5C
- Base Offset: 0x5C
- Size: 0x4

|Bits|   Identifier   |Access|Reset|Name|
|----|----------------|------|-----|----|
|31:0|mcu_reset_vector|  rw  | 0x0 |  — |

### mci_error register

- Absolute Address: 0x60
- Base Offset: 0x60
- Size: 0x4

|Bits|     Identifier    |Access|Reset|Name|
|----|-------------------|------|-----|----|
|  0 |  mci_error_fatal  |   r  | 0x0 |  — |
|  1 |mci_error_non_fatal|   r  | 0x0 |  — |

### mcu_config register

- Absolute Address: 0x64
- Base Offset: 0x64
- Size: 0x4

|Bits|            Identifier            |Access|Reset|Name|
|----|----------------------------------|------|-----|----|
|  0 |         mcu_no_rom_config        |  rw  | 0x0 |  — |
|  1 | cptra_ss_mci_boot_seq_brkpoint_i |  rw  | 0x0 |  — |
|  2 |  cptra_ss_lc_Allow_RMA_on_PPD_i  |  rw  | 0x0 |  — |
|  3 |  cptra_ss_lc_ctrl_scan_rst_ni_i  |  rw  | 0x0 |  — |
|  4 |cptra_ss_lc_esclate_scrap_state0_i|  rw  | 0x0 |  — |
|  5 |cptra_ss_lc_esclate_scrap_state1_i|  rw  | 0x0 |  — |

### mci_generic_input_wires register

- Absolute Address: 0x68
- Base Offset: 0x68
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### mci_generic_input_wires register

- Absolute Address: 0x6C
- Base Offset: 0x68
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### mci_generic_output_wires register

- Absolute Address: 0x70
- Base Offset: 0x70
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |   r  | 0x0 |  — |

### mci_generic_output_wires register

- Absolute Address: 0x74
- Base Offset: 0x70
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |   r  | 0x0 |  — |

## fifo_regs register file

- Absolute Address: 0x1000
- Base Offset: 0x1000
- Size: 0x1C

|Offset|    Identifier   |Name|
|------|-----------------|----|
| 0x00 |  log_fifo_data  |  — |
| 0x04 | log_fifo_status |  — |
| 0x08 | itrng_fifo_data |  — |
| 0x0C |itrng_fifo_status|  — |
| 0x10 |   dbg_fifo_pop  |  — |
| 0x14 |  dbg_fifo_push  |  — |
| 0x18 | dbg_fifo_status |  — |

### log_fifo_data register

- Absolute Address: 0x1000
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0| next_char|   r  | 0x0 |  — |
|  8 |char_valid|   r  | 0x0 |  — |

### log_fifo_status register

- Absolute Address: 0x1004
- Base Offset: 0x4
- Size: 0x4

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|  0 |log_fifo_empty|   r  | 0x0 |  — |
|  1 | log_fifo_full|   r  | 0x0 |  — |

### itrng_fifo_data register

- Absolute Address: 0x1008
- Base Offset: 0x8
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|itrng_data|  rw  | 0x0 |  — |

### itrng_fifo_status register

- Absolute Address: 0x100C
- Base Offset: 0xC
- Size: 0x4

|Bits|   Identifier   |Access|Reset|Name|
|----|----------------|------|-----|----|
|  0 |itrng_fifo_empty|   r  | 0x0 |  — |
|  1 | itrng_fifo_full|   r  | 0x0 |  — |
|  2 |itrng_fifo_reset|  rw  | 0x0 |  — |

### dbg_fifo_pop register

- Absolute Address: 0x1010
- Base Offset: 0x10
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0| out_data |   r  | 0x0 |  — |

### dbg_fifo_push register

- Absolute Address: 0x1014
- Base Offset: 0x14
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|  in_data |  rw  | 0x0 |  — |

### dbg_fifo_status register

- Absolute Address: 0x1018
- Base Offset: 0x18
- Size: 0x4

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|  0 |dbg_fifo_empty|   r  | 0x0 |  — |
|  1 | dbg_fifo_full|   r  | 0x0 |  — |
