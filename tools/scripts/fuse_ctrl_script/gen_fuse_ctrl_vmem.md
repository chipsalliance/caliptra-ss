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
    --token-configuration tools/scripts/fuse_ctrl_script/example_tokens.hjson
```

* `--lc-state-def`: Contains information about the life cycle state encoding
* `--mmap-def`: Defines the format of the vmem file.
* `--lc-state`: The desired life cycle state. This value is encoded by the script.
* `--lc-cnt`: The desired raw life cycle counter. This value is encoded by the script.
* `--token-configuration`: File that consists of one or multiple raw unlock tokens.
