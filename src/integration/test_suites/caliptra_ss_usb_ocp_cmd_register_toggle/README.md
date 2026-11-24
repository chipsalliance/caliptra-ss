# OCP Recovery command-register toggle stimulus

This standalone testcase targets register-field transitions, not a complete
recovery flow or production firmware. It is independent of the FIFO boundary
and executable multi-stage tests. No INDIRECT_FIFO command is issued.

The existing recovery-init MCU firmware services USB. The C source here runs
on the **Caliptra core**, selected by `CALIPTRA_TESTNAME`. It writes masked
values through the CPU interface and verifies their storage before the host
checks the complete USB response against an independently constructed snapshot.

## Selected fields

OCP Recovery v1.1 Sections 9.1/9.2 define the following offsets and masks.
Address macros identify the CPU register locations; no RTL reset values are
used as expected data.

| Target | Command | Byte offset | Mutable mask | Selected fields |
| ---: | --- | ---: | --- | --- |
| 0 | PROT_CAP | 8 | `0x1FFF0000` | 13 defined capability bits; version preserved |
| 1 | PROT_CAP | 12 | `0x00FFFFFF` | CMS count, response-time exponent, heartbeat-period exponent |
| 2 | RECOVERY_CTRL | 0 | `0x000F03FF` | CMS storage, legal image selections 0/1/2, activation 0/0x0F |
| 3 | RECOVERY_STATUS | 0 | `0x0000FFFF` | Legal status, image index, vendor status |
| 4 | DEVICE_STATUS | 0 | `0x00FF000F` | Legal status and defined/vendor recovery-reason byte |
| 5 | HW_STATUS | 0 | `0x00FFFF07` | Three hardware flags, vendor status, legal composite temperature |

Each target uses five phases: clear, seeded-random, directed high, complementary
or alternate legal pattern, clear. Firmware and host command acknowledgments
are generation-qualified, including an explicit command-release acknowledgment.
Original values are restored and checked through USB before the next target.
The host requires **both rising and falling transitions on all 98 selected
bits**, failing if any is missing. Random stimulus alone cannot establish pass.

Status, temperature, image-selection and activation encodings avoid reserved
values. Device reasons are populated only in the states defined by Table 2.
Intermediate capability advertisements and CMS counts are controlled storage
snapshots, not claims that every advertised feature or CMS is implemented.
No newly advertised optional command is exercised under those temporary
profiles; the original capability profile is restored first.

## Explicit exclusions

- Fixed PROT_CAP identity/version and reserved bits are preserved.
- DEVICE_STATUS.PROT_ERROR is hardware-owned and clear-on-USB-read; this test
  does not directly write it or claim its toggle closure. Existing error and
  clear-on-read scenarios remain separate.
- Reserved recovery-reason bits are not toggled.
- DEVICE_STATUS heartbeat is CPU-read-only in the register definition
  (`third_party/usb2/systemrdl/usb_ocp_recovery_reg.rdl`, DEVICE_STATUS_1).
  The current integration has no heartbeat producer. Complete DEVICE_STATUS
  snapshots check that the heartbeat bytes remain unchanged while the mutable
  status/reason fields change; no heartbeat toggle closure is claimed.
- Variable-length vendor payloads and their length fields are excluded; the
  campaign requires initial 7-byte DEVICE_STATUS and 4-byte HW_STATUS responses
  and advertised HW_STATUS support.
- RECOVERY_CTRL values are **firmware-written storage/readback stimulus**.
  Unsupported CMS routing/error policy, valid host selection of every region,
  host-triggered activation semantics and the known CMS bug are not closed.
  OCP_CMD_010 remains separate; no RTL fix or expected-failure suppression is
  introduced. The protocol stall matrix currently exercises reserved image
  selection, not an exhaustive CMS-discovery sweep.
- A host-observed value transition is not a measured internal VDB toggle
  percentage. Internal coverage improvement requires a coverage-enabled
  regression and comparison with its baseline VDB.

## Running and validation

```sh
ss_build -tc caliptra_ss_usb_ocp_cmd_register_toggle -to 8000000
```

The default validation run follows the simulation runner's no-coverage/no-wave
settings. `REGISTER_SWEEP_TARGET_PASS` reports each restored target and its
observed rise/fall masks. `REGISTER_SWEEP_PASS` is emitted only after all six
targets pass and normal MCU teardown is requested.

The corrected run `20261120.234848` passed with seed 1 and package 385:
six target-pass markers, `REGISTER_SWEEP_PASS registers=5 targets=6
checked_bits=98 phases_per_target=5`, and `TESTCASE PASSED`. Firmware restored
each target and normal simulation teardown completed. UVM reported zero
warnings, errors and fatals; simulation metadata reports `PASSED` and
returncode 0. Simulation took 1395 seconds; compilation took 285 seconds.
No VDB coverage percentage or existing CMD-item closeout is claimed.

The first run (`20261120.231137`, seed 1, package 384) passed the first five
targets, then failed CPU readback when the test incorrectly attempted to write
the read-only heartbeat field. The corrected campaign excludes those twelve
bits from the transition count and retains whole-response stability checks.
The corrected run also passed HW_STATUS and final teardown.

## Relationship to the CMD request

The colleague's a/b/c list describes implementation approaches, not three
mandatory testcases. This testcase implements approach (c), following the
subsequent five-register set/clear recommendation. The existing command-handling,
activation and W1DC scenarios are not replaced or claimed as newly validated.
CMS discovery/selection is not a storage-toggle check: exercising its routing
and known error-reporting bug requires separate command-policy coverage.
