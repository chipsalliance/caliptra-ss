## Generate `fuse_ctrl` VMEM

Generates a VMEM memory image that can be loaded into `fuse_ctrl`.

### Usage

To create `otp-img.24.vmem`, execute the following:

```sh
cd ${CALIPTRA_SS_ROOT}
python3 -m pip install -r tools/scripts/fuse_ctrl_script/requirements.txt
./tools/scripts/fuse_ctrl_script/gen_fuse_ctrl_vmem.py \
    --lc-state-def tools/scripts/fuse_ctrl_script/lc_ctrl_state.hjson \
    --mmap-def src/fuse_ctrl/data/otp_ctrl_mmap.hjson \
    --lc-state "PROD" --lc-cnt 5 \
    --token-name "CPTRA_SS_PROD_TO_PROD_END_TOKEN" --token-value 0x0000000
```

* `--lc-state-def`: Contains information about the life cycle state encoding
* `--mmap-def`: Defines the format of the vmem file.
* `--lc-state`: The desired life cycle state. This value is encoded by the script.
* `--lc-cnt`: The desired raw life cycle counter. This value is encoded by the script.
* `--token-name`: The token name we want to set.
* `--token-value`: The raw token value. This value is hashed, scrambled, and then written into the memory file.
