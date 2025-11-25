![OCP Logo](./images/OCP_logo.png)

<p style="text-align: center;">Caliptra Subsystem Release Checklist</p>

<p style="text-align: center;">Version 2p1</p>

<div style="page-break-after: always"></div>

# Overview

This document provides the signoff checklist that is used when finalizing any Caliptra Subsystem release version.

# Release Creation

## Versioning

Caliptra Core releases may be created for new major, minor, or patch versions, as described in the [Caliptra Core Release Checklist](https://github.com/chipsalliance/caliptra-rtl/blob/main/docs/CaliptraReleaseChecklist.md). The version number is reflected in the [CPTRA_HW_REV_ID](https://chipsalliance.github.io/caliptra-rtl/main/internal-regs/?p=clp.soc_ifc_reg.CPTRA_HW_REV_ID) register. Caliptra Subsystem major and minor releases follow any Caliptra Core releases, and version numbers are coupled. In some scenarios, Caliptra Subsystem might advance in version when Caliptra Core does not. For example, adding a new recovery interface IP would require a new Caliptra Subsystem minor revision release, or a bug fix would require a Caliptra Subsystem patch release. In these scenarios, any subsequent Caliptra Core release will be fast forwarded to regain major and minor version number correlation. Caliptra Core patch release versions will not be fast forwarded to match Caliptra Subsystem patch versions, however.
For example, the following hypothetical sequence of versions (in chronological release order) is possible:
| Core | Subsystem | Description |
| :--- | :--- | :--- |
| 5.0.0 | 5.0.0 | Initial release of major version "5". |
| 5.1.0 | 5.1.0 | Release of major version "5" with minor version "1". |
| 5.0.1 | 5.0.1 | Caliptra core version 5.0.0 receives a patch update, and Caliptra Subsystem is released with a new version to consume the core patch. |
| 5.1.0 | 5.2.0 | Caliptra Subsystem is released with major version "5" and minor version "2", but Caliptra core is unchanged, so Subsystem release contains version 5.1.0 of core. |
| 5.1.0 | 5.1.1 | Caliptra Subsystem version 5.1 is patched with a bug fix, but Caliptra core is unchanged, so Subsystem release contains version 5.1.0 of core. |
| 5.3.0 | 5.3.0 | Caliptra Core is released with new minor version, which is fast forwarded to match the next available minor version of Caliptra Subsystem. Caliptra Subsystem is released with the same minor version after bringing in the updated Caliptra core. |
| 5.1.1 | 5.1.2 | Caliptra core version 5.1 is patched with its first bug fix. Caliptra Subsystem version 5.1 updates Caliptra core to receive the bug fix, but Subsystem has already been patched once, so Subsystem release 5.1.2 contains version 5.1.1 of core. |

Caliptra Subsystem release versions also follow the same procedure for pre-release versions (a.k.a. "Release Candidates") and documentation updates as Caliptra RTL. Refer to the [Caliptra Core Release Checklist](https://github.com/chipsalliance/caliptra-rtl/blob/main/docs/CaliptraReleaseChecklist.md) for details on these processes.

Steps described in this document are followed for each Subsystem release other than documentation-only updates.

NOTE: On version numbering; Caliptra Subsystem 2.0 release did not originally follow the aforementioned convention. It was released following a format of `css_gen<Caliptra RTL version>_v<MAJOR>.<MINOR>`. This numbering is deprecated, but the original 2.0 version tag remains for legacy reasons and the original patch and release branches are: 
  * `release_css_gen2_v1.0` (tip of this branch is tagged as [css-gen2-v1.0](https://github.com/chipsalliance/caliptra-ss/releases/tag/css-gen2-v1.0))
  * `patch_ss_v1p0` (contains all subsequent patches to Caliptra Subsystem, v2.0 (aka Gen2 v1.0))

## Branches

Each major and minor release is created as a tag on the branch `main` of the caliptra-ss repository. The tag is created using GitHub's repository release tagging feature, which also generates a zip file containing all of the code and documentation for that release. After tagging the release, any subsequent commits to `main` are pursuant to development efforts on future release versions, so the tagged release must be used to download the official release code.

When necessary, a patch release may be applied retroactively to earlier versions of Caliptra or Caliptra Subsystem. In this case, a new branch is created to contain the patched code base. Patch release branches follow the naming convention, `patch_ss_v<MAJOR>.<MINOR>`, to indicate which version is being patched. After the patch release checklist is finalized for a specified release, a tag is created on the patch branch to indicate the full version number of that patch. Thus, any patch release is created as a tag on the same branch, with an incrementing patch version number.

## Steps

For each release, the following steps are followed to ensure code functionality and quality.

- Ensure all critical [issues](https://github.com/chipsalliance/caliptra-ss/issues) and [Pull Requests](https://github.com/chipsalliance/caliptra-ss/pulls) are closed
- Verify expected checks and scripts are in place
  - Audit pipelines: Coverage logging enabled
  - Audit pipelines: File list checks updated
  - Audit pipelines: License header check targets updated
  - Audit pipelines: RDL generator script is updated
  - Audit pipelines: RDL file checker is updated
  - Audit pipelines: Promote pipeline synth check enabled
  - Audit pipelines: Promote pipeline lint check enabled (and test a false-negative)
  - Audit pipelines: Promote pipeline L0 regression list updated
  - Audit pipelines: Promote pipeline L0 regression enabled
  - Audit pipelines: Promote pipeline unit tests enabled
  - Audit pipelines: Nightly pipeline firmware regression test list updated
  - Audit pipelines: Nightly pipeline firmware regression test list enabled
  - Audit pipelines: Nightly pipeline unit testbench regression test list updated
  - Audit pipelines: Nightly pipeline unit testbench regression test list enabled
  - Audit pipelines: Nightly pipeline UVM UNIT regressions test list updated
  - Audit pipelines: Nightly pipeline UVM UNIT regressions enabled
  - Audit pipelines: Nightly pipeline UVM TOP regression test list updated
  - Audit pipelines: Nightly pipeline UVM TOP regression enabled
  - Audit pipelines: Nightly pipeline UVM TOP (ROM) regression enabled
- Audit RTL and testbenches for FIXME/TODO items
- Pre-Silicon Regressions
  - [L0 regression](../src/integration/stimulus/L0_Promote_caliptra_ss_top_tb_regression.yml)
  - Directed/Random regression per the [Test Plan](./Caliptra_Gen2_SS_TestPlan.xlsx)
    - [L1 Directed regression](../src/integration/stimulus/L1_Nightly_Directed_Strict_caliptra_ss_top_tb_regression.yml)
    - [L1 Directed Pseudo-random regression](../src/integration/stimulus/L1_Nightly_Directed_caliptra_ss_top_tb_regression.yml)
    - [L1 Random regression](../src/integration/stimulus/L1_Nightly_Random_caliptra_ss_top_tb_regression.yml)
    - [L1 JTAG tests](../src/integration/stimulus/L1_JTAG_caliptra_ss_top_tb_regression.csv)
- Coverage Review
  - Coverage database is manually reviewed to ensure all required coverpoints are exercised
- FPGA Validation
  - Latest RTL is tested in FPGA
- Submodule updates:
  - i3c-core
  - caliptra-rtl
- Register updates:
  - [HW_REV_ID](https://chipsalliance.github.io/caliptra-ss/main/regs/?p=soc.mci_top.mci_reg.HW_REV_ID): Update version information according to the defined field mapping to match current release
  - [HW_CONFIG0](https://chipsalliance.github.io/caliptra-ss/main/regs/?p=soc.mci_top.mci_reg.CPTRA_HW_CONFIG): Update any fields to indicate a change in Caliptra capabilities
  - [HW_CONFIG1](https://chipsalliance.github.io/caliptra-ss/main/regs/?p=soc.mci_top.mci_reg.CPTRA_HW_CONFIG): Update any fields to indicate a change in Caliptra capabilities
- Lint review:
  - Lint must be completely clean after applying policies and waivers described in [Caliptra Subsystem Integration Specification](./CaliptraSSIntegrationSpecification.md#Recommended-LINT-rules)
- CDC review:
  - All clock crossings are safely synchronized, appropriate constraints are defined
- RDC review
  - All reset domain crossings are safely managed by hardware controls or reviewed and waived
- Formal Verification review
  - Formal test plans for cryptographic blocks are executed and pass
- Update documentation
  - Update lint rules in integration specification
  - Core logic changes documented in the [CaliptraSSHardwareSpecification](./CaliptraSSHardwareSpecification.md)
  - [README](../README.md) updates
  - Add latest synthesis results to the [CaliptraSSIntegrationSpecification](./CaliptraSSIntegrationSpecification.md##synthesis)
  - Update [Release_Notes](../Release_Notes.md)
  - Tag the main branch on GitHub to generate an official release
  - Generate version-specific registers documentation page in the [Register Documentation Workflow](./.github/workflows/doc-gen.yml)
