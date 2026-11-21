# caliptra_ss_usb_hs_dev_err_toggle

Sends a stale DATA PID so the device's endpoint data toggle is out of step, on USBDC0 EP1 at High Speed.

## Coverage target

`usb_transfer_outcome_cg.cp_errortype` bin **`wrong_data_toggle` (0xF)** of
`src/usb/coverage/usb_dev_ep_cov.sv`, assigned at `usb_pie.m.vhdl` line 2917.

The bin was at zero before this test existed, because nothing in the
regression ever produced a protocol error on a device endpoint.

## Mechanism

No exception at all. A plain, well formed **DATA1** packet is driven directly
on the packet sequencer, with `attach_exception == 0`. The clean reference
transfer immediately before it leaves the endpoint expecting DATA0, so a DATA1
arrival is exactly the toggle mismatch `usb_pie.m.vhdl:2917` keys on, and the
packet itself is perfectly legal on the wire.

**Why not an exception.** The first version expressed the skew as
`error_kind == PACKET_FIELD_ERROR` with `field_id == PID_NAME` on a DATA0
carrier. The VIP forbids that combination - its own legality constraint at
`sverilog/src/com/svt_usb_packet_exception.svp:3163` reads:

```
if (xact.pid_type == svt_usb_packet::DATA)
  error_kind inside {CRC_ERROR, PHYSICAL_ERROR, ILLEGAL_DATA_PID_ERROR,
                     PID_CHECK_ERROR, LENGTH_ERROR, NO_OP_ERROR};
```

`PACKET_FIELD_ERROR` is not in that set, so pinning it against a USB 2.0 DATA
packet is an unsatisfiable constraint and the solver fails outright. Sending
the DATA1 as-is reaches the same device-side condition, so nothing is lost.

**Stated assumption.** Driving on the packet sequencer bypasses the transfer
layer, so the VIP's own per-endpoint toggle tracking does not rewrite the PID -
the same property `caliptra_ss_usb_ocp_directed_packet_sequence` relies on.
What cannot be confirmed from documentation alone is whether the hub forwards
an out-of-turn DATA packet that is not preceded by its own OUT token in the
same microframe. If the bin stays open on the first run, the next step is to
precede the DATA1 with a directed OUT token to the same address and endpoint.


The post-injection clean transfer matters more here than in any other test in
the family: the device ACKs the stale packet and discards the payload (USB 2.0
section 8.6), so if the toggles stayed out of step the endpoint would be
silently dead while the wire still looked healthy.

## Suppressed VIP check

This is the only test in the family that relaxes a VIP check. In
`end_of_elaboration_phase` it sets the link check `tend_to_end_delay_check` to
`svt_err_check_stats::EXPECTED`.

A device that receives a data packet with the wrong toggle must discard it and
return **no handshake** (USB 2.0 section 8.6.3). That silence is exactly what
`pie_errortype = 0xF` reports, and it is the bin this test exists to close. The
VIP link layer cannot know the DATA1 was deliberately out of turn, so it starts
its End-to-end Signal Delay timer on that packet and fails when nothing
answers:

```
440411.551 ns  exec_sof WARNING - microframe boundary missed
442111.551 ns  tend_to_end_delay_check FAIL - "Response packet not received
               within the expiry of End to End Delay Timer"
502305.000 ns  MCU: EP1 OUT completion 1 - 1024 bytes
```

The EP1 completion *after* the failure is the point: the endpoint recovered and
the clean reference transfer went through. Without the suppression the test is
unpassable by construction.

Scope is deliberately narrow - this one check, this one test. The other eight
suites are left strict. Their corruptions are also unanswered, but they pass as
they stand, so relaxing them would only mask real regressions.

Note that SVT checks are **not** suppressible via
`set_report_severity_id_override()`; SVT fires them through its own
`svt_err_check_stats` infrastructure, bypassing the UVM report handler. The
supported API is `chk_cov_mgr.find()` + `set_default_fail_effect()`, and it must
run in `end_of_elaboration_phase` once `chk_cov_mgr` is populated. Same pattern
as `caliptra_ss_usb_fs_dev_lpm_l1_test`, `caliptra_ss_usb_dev_reg_rw_test` and
`caliptra_ss_usb_hs_host_remotewakeup_test`.

## Run

```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_toggle_test
```

## Where the detail lives

The RTL derivation of the 16 `pie_errortype` codes, the verified SVT VIP
exception field model, the list of codes that were removed from collection as
unreachable, and the reason the corrupted transfer is expected to fail are all
documented once in **`docs/CaliptraSSUSBErrorInjection.md`**. This family of
nine tests shares all of it; only the table above is specific to this suite.

Per-file detail:

- sequence header - why this particular bin needs this particular stimulus
- `caliptra_ss_usb_err_inject_base_sequence.svh` - shared helpers and the
  full code legend
- firmware `.c` / `libs/usb/usb_err_inject_fw_common.h` - the endpoint
  arming policy

<!-- File contains AI-generated response based on internal company sources -->
