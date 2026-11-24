# USB OCP FIFO boundaries: FIFO_001-005

This directed campaign runs five independently checked scenarios in one USB
session. It reuses recovery-init MCU firmware and the recovery scoreboard.
The C file in this directory runs on the **Caliptra core**, selected by
`CALIPTRA_TESTNAME`; it is not MCU firmware.

| Test-plan item | Stimulus and checks |
| --- | --- |
| FIFO_001 | One 48-byte write; WRITE_INDEX=12, terminal publication, full firmware content verification, EMPTY and RECOVERY_PENDING. |
| FIFO_002 | IMAGE_SIZE=1 DWORD; one successful 4-byte write, WRITE_INDEX=1, publication, content verification, EMPTY and controlled test-firmware completion. |
| FIFO_003 | One maximum legal aligned chunk followed by three bytes; rounded terminal WRITE_INDEX, no early publication, byte ordering and zero-filled unused terminal byte verified by firmware. |
| FIFO_004 | Two chunks each **exactly** the discovered `wMaxWrTransferSize`; check every successful transfer and WRITE_INDEX increment. A smaller minimum-of-limits chunk does not satisfy this case. |
| FIFO_005 | Fill exactly 256 bytes with IMAGE_SIZE=65 DWORDs; check no premature publication, FULL at 256 bytes, publication, first-window drain to EMPTY, deassertion, then a 4-byte next window with fresh publication and final drain. |

Firmware consumption is held with generation-qualified test commands until the
host has observed indices and publication. Firmware discovers IMAGE_SIZE and
FIFO capacity through recovery registers and verifies every DWORD using
`0xC0DE0000 | index`. Each case emits its own `OCP_FIFO_00N_PASS` marker only
after firmware verification, final EMPTY and RECOVERY_PENDING.

This is a test-firmware transport/content check, not production authentication
or executable-image coverage. FIFO_002 intentionally uses controlled completion
rather than claiming a four-byte payload is valid production firmware.

## Requirements and scope

- OCP Recovery v1.1 Sections 8.5.1 and 9.2 define advertised USB write limits,
  DWORD image sizes, FIFO indices and non-DWORD-aligned writes.
- USB 2.0 Section 5.5 distinguishes a control transfer from its DATA packets.
- Publication and full-capacity behavior follow this project's FIFO service-window
  contract, as exercised by the existing FIFO ring test. This is **not** a
  conformance claim for OCP Section 8.2.5's reserved-slot ring policy.
- The 256-byte target comes from FIFO_005's test-plan requirement, not an
  RTL-derived expectation. The campaign explicitly fails its precondition if
  discovered capacity is not 256 bytes, if two advertised maximum writes do
  not fit, or if another advertised limit prohibits that exact chunk size.
- The 200-us publication and 20-ms firmware bounds are test liveness bounds,
  not specification-defined timing requirements.

Run with the initialized workspace:

```sh
ss_build -tc caliptra_ss_usb_ocp_fifo_boundaries -to 8000000
```

## Validation

The directed baseline **passed** on upstream base `6fed5199` with the pinned USB
submodule `9a706d9f`, USB package version 383, seed 1, run `20261120.214040`.
VCS recompiled the USB package. Both firmwares compiled successfully.

| Pass marker | Bytes | DWORDs | Chunks |
| --- | ---: | ---: | ---: |
| `OCP_FIFO_001_PASS` | 48 | 12 | 1 |
| `OCP_FIFO_002_PASS` | 4 | 1 | 1 |
| `OCP_FIFO_003_PASS` | 67 | 17 | 2 |
| `OCP_FIFO_004_PASS` | 128 | 32 | 2 |
| `OCP_FIFO_005_PASS` | 260 | 65 | 5 |

All five markers confirm checked indices, publication, firmware content and
RECOVERY_PENDING. Final result: `TESTCASE PASSED`, metadata return code 0,
**UVM warning/error/fatal counts 0/0/0**. Simulation wall time was 1,910 seconds
(about 32 minutes); build time was 299 seconds. The run directory occupied
22 MB, with no wave or coverage collection.

Whitespace, exact master/Directed/Strict registration order and repository
unused-test checks passed (339 used tests). This is one fixed directed baseline,
not a randomized sweep or production authentication validation.
