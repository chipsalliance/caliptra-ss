## KMAC KAT Smoke Test

This test indirectly tests whether the KMAC instantiated inside the LCC produces the correct output.

The reference hashes are placed as unlock tokens into the `otp-img.2048.vmem` file.
These hashes are generated using the following code snippet inside the `gen_fuse_ctrl_vmem.py` script:
```python
from Crypto.Hash import cSHAKE128

value = int(token_value, 0)
data = value.to_bytes(16, byteorder='little')
custom = 'LC_CTRL'.encode('UTF-8')
shake = cSHAKE128.new(data=data, custom=custom)
digest = int.from_bytes(shake.read(16), byteorder='little')
```

The `smoke_test_lcc_kmac_kat` test writes the unhashed tokens to the LCC which uses the KMAC core to create the hashed tokens.
Then, the test tries several state transitions.
If the state transitions succeed, the hashing was correct.

### Test Usage

```sh
cd ${CALIPTRA_SS_ROOT}
python3 -m pip install -r tools/scripts/fuse_ctrl_script/requirements.txt
./tools/scripts/fuse_ctrl_script/gen_fuse_ctrl_vmem.py \
    --lc-state-def tools/scripts/fuse_ctrl_script/lc_ctrl_state.hjson \
    --mmap-def src/fuse_ctrl/data/otp_ctrl_mmap.hjson \
    --lc-state "TEST_LOCKED0" --lc-cnt 5 \
    --token-configuration src/integration/test_suites/smoke_test_lcc_kmac_kat/test_unlock_token.hjson \
    -o src/fuse_ctrl/data/otp-img.2048.vmem
```
Please be aware that this script overwrites the default `src/fuse_ctrl/data/otp-img.2048.vmem` file.

Then, execute this test.
