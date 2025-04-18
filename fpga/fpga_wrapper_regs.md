<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: caliptra_fpga_realtime_regs
  - caliptra_fpga_realtime_regs.rdl
-->

## caliptra_fpga_realtime_regs address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0xA401101C

|  Offset  |  Identifier  |Name|
|----------|--------------|----|
|0xA4010000|interface_regs|  — |
|0xA4011000|   fifo_regs  |  — |

## interface_regs register file

- Absolute Address: 0xA4010000
- Base Offset: 0xA4010000
- Size: 0x130

|Offset|         Identifier        |Name|
|------|---------------------------|----|
| 0x000|         fpga_magic        |  — |
| 0x004|        fpga_version       |  — |
| 0x008|          control          |  — |
| 0x00C|           status          |  — |
| 0x010|           pauser          |  — |
| 0x014|       itrng_divisor       |  — |
| 0x018|        cycle_count        |  — |
| 0x030|   generic_input_wires[0]  |  — |
| 0x034|   generic_input_wires[1]  |  — |
| 0x038|  generic_output_wires[0]  |  — |
| 0x03C|  generic_output_wires[1]  |  — |
| 0x040|      cptra_obf_key[0]     |  — |
| 0x044|      cptra_obf_key[1]     |  — |
| 0x048|      cptra_obf_key[2]     |  — |
| 0x04C|      cptra_obf_key[3]     |  — |
| 0x050|      cptra_obf_key[4]     |  — |
| 0x054|      cptra_obf_key[5]     |  — |
| 0x058|      cptra_obf_key[6]     |  — |
| 0x05C|      cptra_obf_key[7]     |  — |
| 0x060|   cptra_csr_hmac_key[0]   |  — |
| 0x064|   cptra_csr_hmac_key[1]   |  — |
| 0x068|   cptra_csr_hmac_key[2]   |  — |
| 0x06C|   cptra_csr_hmac_key[3]   |  — |
| 0x070|   cptra_csr_hmac_key[4]   |  — |
| 0x074|   cptra_csr_hmac_key[5]   |  — |
| 0x078|   cptra_csr_hmac_key[6]   |  — |
| 0x07C|   cptra_csr_hmac_key[7]   |  — |
| 0x080|   cptra_csr_hmac_key[8]   |  — |
| 0x084|   cptra_csr_hmac_key[9]   |  — |
| 0x088|   cptra_csr_hmac_key[10]  |  — |
| 0x08C|   cptra_csr_hmac_key[11]  |  — |
| 0x090|   cptra_csr_hmac_key[12]  |  — |
| 0x094|   cptra_csr_hmac_key[13]  |  — |
| 0x098|   cptra_csr_hmac_key[14]  |  — |
| 0x09C|   cptra_csr_hmac_key[15]  |  — |
| 0x0A0|   cptra_obf_uds_seed[0]   |  — |
| 0x0A4|   cptra_obf_uds_seed[1]   |  — |
| 0x0A8|   cptra_obf_uds_seed[2]   |  — |
| 0x0AC|   cptra_obf_uds_seed[3]   |  — |
| 0x0B0|   cptra_obf_uds_seed[4]   |  — |
| 0x0B4|   cptra_obf_uds_seed[5]   |  — |
| 0x0B8|   cptra_obf_uds_seed[6]   |  — |
| 0x0BC|   cptra_obf_uds_seed[7]   |  — |
| 0x0C0|   cptra_obf_uds_seed[8]   |  — |
| 0x0C4|   cptra_obf_uds_seed[9]   |  — |
| 0x0C8|   cptra_obf_uds_seed[10]  |  — |
| 0x0CC|   cptra_obf_uds_seed[11]  |  — |
| 0x0D0|   cptra_obf_uds_seed[12]  |  — |
| 0x0D4|   cptra_obf_uds_seed[13]  |  — |
| 0x0D8|   cptra_obf_uds_seed[14]  |  — |
| 0x0DC|   cptra_obf_uds_seed[15]  |  — |
| 0x0E0| cptra_obf_field_entropy[0]|  — |
| 0x0E4| cptra_obf_field_entropy[1]|  — |
| 0x0E8| cptra_obf_field_entropy[2]|  — |
| 0x0EC| cptra_obf_field_entropy[3]|  — |
| 0x0F0| cptra_obf_field_entropy[4]|  — |
| 0x0F4| cptra_obf_field_entropy[5]|  — |
| 0x0F8| cptra_obf_field_entropy[6]|  — |
| 0x0FC| cptra_obf_field_entropy[7]|  — |
| 0x100|          lsu_user         |  — |
| 0x104|          ifu_user         |  — |
| 0x108|          clp_user         |  — |
| 0x10C|      soc_config_user      |  — |
| 0x110|      sram_config_user     |  — |
| 0x114|      mcu_reset_vector     |  — |
| 0x118|         mci_error         |  — |
| 0x11C|         mcu_config        |  — |
| 0x120| mci_generic_input_wires[0]|  — |
| 0x124| mci_generic_input_wires[1]|  — |
| 0x128|mci_generic_output_wires[0]|  — |
| 0x12C|mci_generic_output_wires[1]|  — |

### fpga_magic register

- Absolute Address: 0xA4010000
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|   Reset  |Name|
|----|----------|------|----------|----|
|31:0|fpga_magic|   r  |0x52545043|  — |

#### fpga_magic field

<p>Ascii "CPTR" to check that the image is valid.</p>

### fpga_version register

- Absolute Address: 0xA4010004
- Base Offset: 0x4
- Size: 0x4

|Bits| Identifier |Access|Reset|Name|
|----|------------|------|-----|----|
|31:0|fpga_version|   r  | 0x0 |  — |

#### fpga_version field

<p>Git commit of HEAD the FPGA was built with.</p>

### control register

- Absolute Address: 0xA4010008
- Base Offset: 0x8
- Size: 0x4

|Bits|         Identifier        |Access|Reset|Name|
|----|---------------------------|------|-----|----|
|  0 |       cptra_pwrgood       |  rw  | 0x0 |  — |
|  1 |       cptra_ss_rst_b      |  rw  | 0x0 |  — |
|  2 |   cptra_obf_uds_seed_vld  |  rw  | 0x0 |  — |
|  3 |cptra_obf_field_entropy_vld|  rw  | 0x0 |  — |
|  4 | force_mcu_dmi_core_enable |  rw  | 0x0 |  — |
|  5 |force_mcu_dmi_uncore_enable|  rw  | 0x0 |  — |
|  6 |      bootfsm_brkpoint     |  rw  | 0x0 |  — |
|  7 |      ss_debug_intent      |  rw  | 0x0 |  — |

### status register

- Absolute Address: 0xA401000C
- Base Offset: 0xC
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

- Absolute Address: 0xA4010010
- Base Offset: 0x10
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|  pauser  |  rw  | 0x0 |  — |

### itrng_divisor register

- Absolute Address: 0xA4010014
- Base Offset: 0x14
- Size: 0x4

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|itrng_divisor|  rw  | 0x0 |  — |

### cycle_count register

- Absolute Address: 0xA4010018
- Base Offset: 0x18
- Size: 0x4

|Bits| Identifier|Access|Reset|Name|
|----|-----------|------|-----|----|
|31:0|cycle_count|   r  | 0x0 |  — |

### generic_input_wires register

- Absolute Address: 0xA4010030
- Base Offset: 0x30
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### generic_input_wires register

- Absolute Address: 0xA4010034
- Base Offset: 0x30
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### generic_output_wires register

- Absolute Address: 0xA4010038
- Base Offset: 0x38
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |   r  | 0x0 |  — |

### generic_output_wires register

- Absolute Address: 0xA401003C
- Base Offset: 0x38
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |   r  | 0x0 |  — |

### cptra_obf_key register

- Absolute Address: 0xA4010040
- Base Offset: 0x40
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_key register

- Absolute Address: 0xA4010044
- Base Offset: 0x40
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_key register

- Absolute Address: 0xA4010048
- Base Offset: 0x40
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_key register

- Absolute Address: 0xA401004C
- Base Offset: 0x40
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_key register

- Absolute Address: 0xA4010050
- Base Offset: 0x40
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_key register

- Absolute Address: 0xA4010054
- Base Offset: 0x40
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_key register

- Absolute Address: 0xA4010058
- Base Offset: 0x40
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_key register

- Absolute Address: 0xA401005C
- Base Offset: 0x40
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_csr_hmac_key register

- Absolute Address: 0xA4010060
- Base Offset: 0x60
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_csr_hmac_key register

- Absolute Address: 0xA4010064
- Base Offset: 0x60
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_csr_hmac_key register

- Absolute Address: 0xA4010068
- Base Offset: 0x60
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_csr_hmac_key register

- Absolute Address: 0xA401006C
- Base Offset: 0x60
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_csr_hmac_key register

- Absolute Address: 0xA4010070
- Base Offset: 0x60
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_csr_hmac_key register

- Absolute Address: 0xA4010074
- Base Offset: 0x60
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_csr_hmac_key register

- Absolute Address: 0xA4010078
- Base Offset: 0x60
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_csr_hmac_key register

- Absolute Address: 0xA401007C
- Base Offset: 0x60
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_csr_hmac_key register

- Absolute Address: 0xA4010080
- Base Offset: 0x60
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_csr_hmac_key register

- Absolute Address: 0xA4010084
- Base Offset: 0x60
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_csr_hmac_key register

- Absolute Address: 0xA4010088
- Base Offset: 0x60
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_csr_hmac_key register

- Absolute Address: 0xA401008C
- Base Offset: 0x60
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_csr_hmac_key register

- Absolute Address: 0xA4010090
- Base Offset: 0x60
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_csr_hmac_key register

- Absolute Address: 0xA4010094
- Base Offset: 0x60
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_csr_hmac_key register

- Absolute Address: 0xA4010098
- Base Offset: 0x60
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_csr_hmac_key register

- Absolute Address: 0xA401009C
- Base Offset: 0x60
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_uds_seed register

- Absolute Address: 0xA40100A0
- Base Offset: 0xA0
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_uds_seed register

- Absolute Address: 0xA40100A4
- Base Offset: 0xA0
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_uds_seed register

- Absolute Address: 0xA40100A8
- Base Offset: 0xA0
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_uds_seed register

- Absolute Address: 0xA40100AC
- Base Offset: 0xA0
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_uds_seed register

- Absolute Address: 0xA40100B0
- Base Offset: 0xA0
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_uds_seed register

- Absolute Address: 0xA40100B4
- Base Offset: 0xA0
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_uds_seed register

- Absolute Address: 0xA40100B8
- Base Offset: 0xA0
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_uds_seed register

- Absolute Address: 0xA40100BC
- Base Offset: 0xA0
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_uds_seed register

- Absolute Address: 0xA40100C0
- Base Offset: 0xA0
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_uds_seed register

- Absolute Address: 0xA40100C4
- Base Offset: 0xA0
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_uds_seed register

- Absolute Address: 0xA40100C8
- Base Offset: 0xA0
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_uds_seed register

- Absolute Address: 0xA40100CC
- Base Offset: 0xA0
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_uds_seed register

- Absolute Address: 0xA40100D0
- Base Offset: 0xA0
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_uds_seed register

- Absolute Address: 0xA40100D4
- Base Offset: 0xA0
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_uds_seed register

- Absolute Address: 0xA40100D8
- Base Offset: 0xA0
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_uds_seed register

- Absolute Address: 0xA40100DC
- Base Offset: 0xA0
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_field_entropy register

- Absolute Address: 0xA40100E0
- Base Offset: 0xE0
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_field_entropy register

- Absolute Address: 0xA40100E4
- Base Offset: 0xE0
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_field_entropy register

- Absolute Address: 0xA40100E8
- Base Offset: 0xE0
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_field_entropy register

- Absolute Address: 0xA40100EC
- Base Offset: 0xE0
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_field_entropy register

- Absolute Address: 0xA40100F0
- Base Offset: 0xE0
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_field_entropy register

- Absolute Address: 0xA40100F4
- Base Offset: 0xE0
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_field_entropy register

- Absolute Address: 0xA40100F8
- Base Offset: 0xE0
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### cptra_obf_field_entropy register

- Absolute Address: 0xA40100FC
- Base Offset: 0xE0
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### lsu_user register

- Absolute Address: 0xA4010100
- Base Offset: 0x100
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0| lsu_user |  rw  | 0x0 |  — |

### ifu_user register

- Absolute Address: 0xA4010104
- Base Offset: 0x104
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0| ifu_user |  rw  | 0x0 |  — |

### clp_user register

- Absolute Address: 0xA4010108
- Base Offset: 0x108
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0| clp_user |  rw  | 0x0 |  — |

### soc_config_user register

- Absolute Address: 0xA401010C
- Base Offset: 0x10C
- Size: 0x4

|Bits|   Identifier  |Access|Reset|Name|
|----|---------------|------|-----|----|
|31:0|soc_config_user|  rw  | 0x0 |  — |

### sram_config_user register

- Absolute Address: 0xA4010110
- Base Offset: 0x110
- Size: 0x4

|Bits|   Identifier   |Access|Reset|Name|
|----|----------------|------|-----|----|
|31:0|sram_config_user|  rw  | 0x0 |  — |

### mcu_reset_vector register

- Absolute Address: 0xA4010114
- Base Offset: 0x114
- Size: 0x4

|Bits|   Identifier   |Access|Reset|Name|
|----|----------------|------|-----|----|
|31:0|mcu_reset_vector|  rw  | 0x0 |  — |

### mci_error register

- Absolute Address: 0xA4010118
- Base Offset: 0x118
- Size: 0x4

|Bits|     Identifier    |Access|Reset|Name|
|----|-------------------|------|-----|----|
|  0 |  mci_error_fatal  |   r  | 0x0 |  — |
|  1 |mci_error_non_fatal|   r  | 0x0 |  — |

### mcu_config register

- Absolute Address: 0xA401011C
- Base Offset: 0x11C
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

- Absolute Address: 0xA4010120
- Base Offset: 0x120
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### mci_generic_input_wires register

- Absolute Address: 0xA4010124
- Base Offset: 0x120
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |  rw  | 0x0 |  — |

### mci_generic_output_wires register

- Absolute Address: 0xA4010128
- Base Offset: 0x128
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |   r  | 0x0 |  — |

### mci_generic_output_wires register

- Absolute Address: 0xA401012C
- Base Offset: 0x128
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   value  |   r  | 0x0 |  — |

## fifo_regs register file

- Absolute Address: 0xA4011000
- Base Offset: 0xA4011000
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

- Absolute Address: 0xA4011000
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0| next_char|   r  | 0x0 |  — |
|  8 |char_valid|   r  | 0x0 |  — |

### log_fifo_status register

- Absolute Address: 0xA4011004
- Base Offset: 0x4
- Size: 0x4

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|  0 |log_fifo_empty|   r  | 0x0 |  — |
|  1 | log_fifo_full|   r  | 0x0 |  — |

### itrng_fifo_data register

- Absolute Address: 0xA4011008
- Base Offset: 0x8
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|itrng_data|  rw  | 0x0 |  — |

### itrng_fifo_status register

- Absolute Address: 0xA401100C
- Base Offset: 0xC
- Size: 0x4

|Bits|   Identifier   |Access|Reset|Name|
|----|----------------|------|-----|----|
|  0 |itrng_fifo_empty|   r  | 0x0 |  — |
|  1 | itrng_fifo_full|   r  | 0x0 |  — |
|  2 |itrng_fifo_reset|  rw  | 0x0 |  — |

### dbg_fifo_pop register

- Absolute Address: 0xA4011010
- Base Offset: 0x10
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0| out_data |   r  | 0x0 |  — |

### dbg_fifo_push register

- Absolute Address: 0xA4011014
- Base Offset: 0x14
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|  in_data |  rw  | 0x0 |  — |

### dbg_fifo_status register

- Absolute Address: 0xA4011018
- Base Offset: 0x18
- Size: 0x4

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|  0 |dbg_fifo_empty|   r  | 0x0 |  — |
|  1 | dbg_fifo_full|   r  | 0x0 |  — |
