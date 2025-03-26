## LCC Transitions Smoke Test

This test checks, whether we can reach the next LC state using an unlock token.
By using the gen_fuse_ctrl_vmem.py script, an arbitrary LC start state can be programmed into the OTP memory.
Then test reads the current state and tries to reach the next state.

For example, to test, whether we can reach `PROD_END` from `PROD`, first call the script:
```sh
cd ${CALIPTRA_SS_ROOT}
python3 -m pip install -r tools/scripts/fuse_ctrl_script/requirements.txt
./tools/scripts/fuse_ctrl_script/gen_fuse_ctrl_vmem.py \
    --lc-state-def tools/scripts/fuse_ctrl_script/lc_ctrl_state.hjson \
    --mmap-def src/fuse_ctrl/data/otp_ctrl_mmap.hjson \
    --lc-state "PROD" --lc-cnt 5 \
    --token-configuration src/integration/test_suites/caliptra_ss_lcc_st_trans/test_unlock_token.hjson \
    -o src/fuse_ctrl/data/otp-img.2048.vmem
```
Please be aware that this script overwrites the default `src/fuse_ctrl/data/otp-img.2048.vmem` file.

When executing the test, the starting state is `PROD` and the test switches to `PROD_END` using the token defined in `test_unlock_token.hjson`.
