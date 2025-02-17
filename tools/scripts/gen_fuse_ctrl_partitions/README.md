## Generate `fuse_ctrl` Partitions

This script generates the configurable (register and partition) blocks for
the instantiation of the `fuse_ctrl`. The basis is a `otp_ctrl_mmap.hjson.tpl`
(see `src/fuse_ctrl/templates`) file in which all the partitions are described.

### Output
Four RTL files alongside their corresponding documentation files are generated
and placed in the following directories:

```
src/fuse_ctrl/rtl
├── otp_ctrl_part_pkg.sv
├── otp_ctrl_core_reg_top.sv
├── otp_ctrl_prim_reg_top.sv
└── otp_ctrl_reg_pkg.sv
src/fuse_ctrl/data
├── otp_ctrl_mmap.hjson
└── otp_ctrl.hjson
src/fuse_ctrl/doc
├── otp_ctrl_digests.md
├── otp_ctrl_field_descriptions.md
├── otp_ctrl_mmap.md
└── otp_ctrl_partitions.md
```

### Vendor-Specific Partitions
By default no vendor-specific partitions (except `vendor_test`) are generated. By setting
the `--num_vendor_fuses N` this behaviour can be overridden and five additional partitions
are added (see `otp_ctrl_mmap.hjson.tpl`):
  - VENDOR_HASHES_MANUF_PARTITION: Contains the first (0-th) vendor public-key hashes.
    Programmable during the manufacturing life-cycle phase.
  - VENDOR_HASHES_PROD_PARTITION: Contains the remaining `N-1` vendor public-key hashes.
    In-field programmable.
  - VENDOR_REVOCATIONS_PROD_PARTITION: Contains `N` sets of revocation bits for each
    vendor public-key.
    In-field programmable.
  - VENDOR_SECRET_PROD_PARTITION: Contains `N` secret vendor-specific fuses.
    In-field programmable.
  - VENDOR_NON_SECRET_PROD_PARTITION: Contains `N` non-secret vendor-specific fuses.
    In-field programmable.

### Execution
```sh
python3 -m pip install -r requirements.txt
./caliptra-ss/tools/scripts/gen_fuse_ctrl_partitions/gen_fuse_ctrl_partitions.py --num_vendor_fuses 16 
```