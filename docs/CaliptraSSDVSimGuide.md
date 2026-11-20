# Running DVSim Regressions with `nightly-runner.yml`

## Overview

The [`.github/workflows/nightly-runner.yml`](../.github/workflows/nightly-runner.yml) workflow executes OpenTitan/Caliptra DVSim regressions using Synopsys VCS inside the Nix `caliptra-dvsim` environment ([`flake.nix`](../flake.nix)) on `caliptra-ss` self-hosted runners.
New contributors can use this workflow to validate a new IP block testbench on a pull request, test another open PR, or register a block to run automatically every night with coverage.

**Current status:** At present, `nightly-runner.yml` runs only `dvsim --version` as a lightweight smoke check to validate the Nix `caliptra-dvsim` environment and self-hosted runner setup.
The regression and coverage commands shown below are examples to use as reference until per-IP DVSim jobs are added to the workflow.

## Prerequisites for a New Block

Before running DVSim on a new IP block (`<block>`), make sure your branch includes:

* **A DVSim configuration file** (typically `src/<block>/dv/<block>_sim_cfg.hjson`) that defines `name`, `dut`, `tb`, `fusesoc_core`, test lists, and imports the shared DVSim configurations under `{CALIPTRA_ROOT}/tools/dvsim/` (automatically symlinked by Nix to `third_party/caliptra-rtl/tools/dvsim`).
* **A FuseSoC core file** (`.core`) for the block RTL and DV testbench matching the `fusesoc_core` target in `<block>_sim_cfg.hjson`.

## Step-by-Step Guide for New Users

Choose one of the workflows below depending on what you want to run.

### Scenario 1: Run DVSim on a Block in Your Own Branch or PR

If your block RTL and DV files are already in your current branch (or already merged into `main`), `actions/checkout@v4` automatically checks out your branch and initializes all submodules recursively.

1. Open `.github/workflows/nightly-runner.yml` and leave the `Checkout branch` step commented out.
2. In the `Run tests` step, update `DVSIM_CMD` to point to your block's `.hjson` simulation configuration:

```yaml
      - name: Run tests
        env:
          DVSIM_CMD: dvsim src/<block>/dv/<block>_sim_cfg.hjson -t vcs -i all --cov
        run: |
          nix develop .#caliptra-dvsim \
            --override-input caliptra-rtl-src "path:$PWD/third_party/caliptra-rtl" \
            --command bash -c '
              export PATH=/usr/bin:/bin:$PATH
              $DVSIM_CMD
            '
```

3. Commit and push your branch, then trigger the workflow manually via `workflow_dispatch` (or, for temporary PR testing, add `pull_request:` under `on:` in your PR branch—subject to maintainer approval for external forks—and remove it before merging).

When bringing up a new block for the first time, it is recommended to iterate in three stages via `DVSIM_CMD`:

1. **Check `.hjson` config parsing (~1s, no VCS build)**: `dvsim src/<block>/dv/<block>_sim_cfg.hjson -t vcs --list`
2. **Run a quick smoke test (~30s)**: `dvsim src/<block>/dv/<block>_sim_cfg.hjson -t vcs -i smoke`
3. **Run the full regression with coverage**: `dvsim src/<block>/dv/<block>_sim_cfg.hjson -t vcs -i all --cov`

### Scenario 2: Run DVSim Against Another Open PR

If you want to run DVSim on code from an existing pull request on `chipsalliance/caliptra-ss` without merging or rebasing that branch locally:

1. Uncomment the `Checkout branch` step in `.github/workflows/nightly-runner.yml` and set `PR` on that single line to the target pull request number:

```yaml
      - name: Checkout branch (PR ${{ env.PR }})
        env:
          PR: 1312
        run: |
          git fetch https://github.com/chipsalliance/caliptra-ss.git pull/$PR/head:pr-$PR
          git checkout pr-$PR
          git submodule update --init --recursive
```

2. Update `DVSIM_CMD` in the `Run tests` step to run the target block's `.hjson` configuration (for example, `dvsim src/uart/dv/uart_sim_cfg.hjson -t vcs -i all --cov`).

### Scenario 3: Add a New Block Permanently to Nightly Regressions

Once your block's DV testbench is merged into `main` and ready to run every night:

1. Add a dedicated job block under `jobs:` in `.github/workflows/nightly-runner.yml` (for example, `dvsim-<block>:`) with a descriptive `name:` such as `DVSIM (<block>)`.
2. Copy the `Setup repository`, `Setup Nix environment`, and `Run tests` steps into that job and set `DVSIM_CMD` to your block's regression command.

Defining one job per IP block allows all blocks to run in parallel across available `caliptra-ss` runners and report independent pass/fail statuses in GitHub Actions.

## Common `dvsim` Flags

* `--version`: Prints the installed `dvsim` version and exits (used as a lightweight runner smoke check).
* `--list` (or `-l`): Parses the `.hjson` configuration, lists available tests and regressions, and exits without invoking VCS.
* `-t vcs`: Selects Synopsys VCS as the simulator tool.
* `-i <item>`: Selects the test or regression group to run (for example, `-i smoke`, `-i uart_smoke`, or `-i all`).
* `--cov`: Enables coverage collection, merging, and report generation.
* `--max-parallel <N>`: Caps the number of concurrent simulation jobs (for example, `--max-parallel 16`).
* `--fixed-seed <S>`: Runs tests with a deterministic seed `<S>` when reproducing a failure.

## How the Workflow Works Under the Hood

Each job executes on a `[caliptra-ss]` self-hosted container runner in three main phases:

1. **Setup repository**: Checks out the repository and recursively initializes all submodules (`third_party/caliptra-rtl`, `third_party/i3c-core`, `third_party/cocotbext-i3c`, and `third_party/usb2`).
2. **Setup Nix environment**: Points the `caliptra-rtl-src` flake input at the local `third_party/caliptra-rtl` checkout and pre-builds the `.#caliptra-dvsim` Nix development shell.
3. **Run tests**: Enters `.#caliptra-dvsim`, prepends `/usr/bin:/bin` to `PATH` so VCS links simulation binaries with the host system toolchain, and executes `$DVSIM_CMD`.

## Runner Environment and Approval Policy

Each `caliptra-ss` self-hosted runner executes in a clean, ephemeral, containerized environment:

* **Single-use ephemeral containers**: Each runner registers with a single-use JIT token, runs exactly one job, and exits; the container is destroyed after the job (`--rm`).
* **Unprivileged isolation**: Jobs run as a non-root user inside an unprivileged (non-`--privileged`) rootless container; nothing persists between jobs.
* **Read-only tool mounts and wiped workspace**: EDA tool installations are mounted read-only.
  The only writable bind mount is the runner's job-local `_work` directory (`$GITHUB_WORKSPACE` / `$RUNNER_TEMP`), which is wiped after every job completes.
* **No host secrets in the container**: Infrastructure credentials (such as the GitHub App private key used to mint JIT tokens) stay on the host and are never exposed inside the runner container.
* **Trigger / approval policy**: To avoid automatically executing untrusted fork PR code on self-hosted runners, `nightly-runner.yml` on `main` is triggered only via `schedule` and `workflow_dispatch` (not `pull_request`).
  Manual runs via `workflow_dispatch` require repository write permissions.
  If a contributor temporarily adds a `pull_request:` trigger on a PR branch for testing, outside-contributor fork PR runs are subject to the repository's GitHub Actions fork-approval settings and require maintainer review before executing.

## Running the CI Setup Locally

On a machine with Nix and Synopsys VCS configured, you can repeat the CI setup procedure locally from the root of a `caliptra-ss` checkout (with submodules initialized):

```bash
nix flake update --override-input caliptra-rtl-src "path:$PWD/third_party/caliptra-rtl"
nix develop .#caliptra-dvsim \
  --override-input caliptra-rtl-src "path:$PWD/third_party/caliptra-rtl" \
  --command bash -c '
    export PATH=/usr/bin:/bin:$PATH
    dvsim src/<block>/dv/<block>_sim_cfg.hjson -t vcs -i smoke
  '
```

**Note:** Because this repository does not currently commit a `flake.lock` file, running `nix flake update` resolves the latest unlocked flake inputs and may pull newer dependency revisions than a previous CI run.

## Workflow Triggers

* **Manual Dispatch (`workflow_dispatch`)**: Once on the default branch, trigger manually from **Actions** -> **Nightly Runner** -> **Run workflow** (requires repository write permissions).
* **Nightly Schedule (`schedule`)**: Once merged into the default branch (`main`), runs automatically every day at `01:00 UTC` (`cron: '0 1 * * *'`).
* **Pull Request (`pull_request`)**: Intentionally disabled on `main` so untrusted fork pull requests do not automatically run on self-hosted runners.
