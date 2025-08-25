
# Zeroization Hardware Changes

The additional circuitry induced by the zeroization flow is lightweight and relatively noninterfering with respect to existing logic.
That is, all the FSM flows present before the introduction of the zeroization feature such as partition initialization, consistency/integrity checks and direct-access reads/writes remain entirely unaltered and function as before.
Below, we list two noticeable changes to the state machines of buffered/unbuffered partitions and the direct-access interface (DAI):

 - _Partition FSMs_: Upon reset, and only if the partition is configured as zeroizable, the partition state machines will now first read the zeroization marker before launching the initialization sequence to determine whether a partition is zeroized which will disable the peroidic consistency/integrity checks.
Three new sequential states are added to both the buffered and unbuffered partitions:
	```
	            + --------------------------------------------------- +
	 ResetSt -> | InitChkZerSt -> InitChkZerWaitSt -> InitChkZerCnfSt | -> InitSt
	            + --------------------------------------------------- +
	```
	- _InitChkZerSt_: Read out the zeroization marker. Wait here until the OTP request has been granted.
	- _InitChkZerWaitSt_: Wait for the OTP response and and write read out marker into a register.
	- _InitChkZerCnfSt_:  Configurations based on the read out and flopped zeroization marker.
- _DAI FSM_: Initiating a zeroization request through the direct-acccess interface comes in the form of a new `DaiZeroize` command and two new FSM states that resemble the existing`DaiRead` and `DaiWrite` flows:
	```
	            + ------------------ +
	 IdleSt  -> | ZerSt -> ZerWaitSt | -> IdleSt
	            + ------------------ +
	```
	- _ZerSt_: Check whether partition is zeroizable and transition into the wait state once the request has been granted.
	- _ZerWaitSt_: Wait for OTP response to the zeroization request.

For a detailed breakdown of the various pre-zeroization flows alongside FSM illustrations, the reader is referred to OpenTitan `otp_ctrl` [documentation](https://opentitan.org/book/hw/top_earlgrey/ip_autogen/otp_ctrl/doc/theory_of_operation.html). 