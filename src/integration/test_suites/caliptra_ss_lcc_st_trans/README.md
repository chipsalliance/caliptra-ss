## LCC Transitions Smoke Test

This test checks, whether we can reach the next LC state using an unlock token.
By using the gen_fuse_ctrl_vmem.py script, an arbitrary LC start state can be programmed into the OTP memory.
Then test reads the current state and tries to reach the next state.

On each test execution, a random LC start state as well as LC counter is generated bz the `gen_fuse_ctrl_vmem.py` script and placed into the `otp-img.2048.vmem` file as well as the `caliptra_ss_lcc_st_trans.h` header.
