#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# 
#
# Licensed under the Apache License, Version 2.0 (the \"License\");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an \"AS IS\" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License."

set -o pipefail    # we still want to catch pipeline failures, but we will handle exit‐codes ourselves

# --- MOCK submit for testing ---
# change "submit" to submit_test if you want to test changes to this script
submit_test() {
  sleep_time=$(( (RANDOM % 30) + 1 ))
  exit_code=$(( RANDOM % 2 ))
  echo "[MOCK submit] Sleeping for $sleep_time seconds, will exit with $exit_code"
  sleep "$sleep_time"
  return "$exit_code"
}


# 1) build up any coverage args
cov_args=()
if [[ -n "${COVERAGE_DIR_PATH:-}" ]]; then
  echo "COVERAGE_DIR_PATH is: ${COVERAGE_DIR_PATH}"
  cov_args=( -c -cov_dir ${COVERAGE_DIR_PATH} )
else
  echo "COVERAGE_DIR_PATH is not defined."
fi

# 2) your test list
tests=(
  "smoke_test_jtag_uds_prog:520000"
  "smoke_test_jtag_manuf_dbg:520000"
  "smoke_test_jtag_prod_dbg:10000000"
  "smoke_test_jtag_lcc_registers:185000"
  "caliptra_ss_jtag_lcc_st_trans:220000"
  "smoke_test_jtag_mcu_bp:220000"
  "smoke_test_jtag_mcu_intent:220000"
  "smoke_test_jtag_mcu_unlock:220000"
  "smoke_test_jtag_mcu_sram:220000"
)

overall_rc=0
max_parallel=5 # Configurable number of tests running in parallel

echo "MAX PARALLEL TESTS: $max_parallel"

# Arrays to track PIDs and commands
declare -A pid_to_cmd
declare -A pid_to_tc

running=0
pids=()
kicked_off=0

# Function to wait for a PID, print result, and update overall_rc
wait_and_report() {
  local pid=$1
  # Check if PID is empty and exit if it is
  if [[ -z "$pid" ]]; then
    return
  fi
  wait "$pid"
  local rc=$?
  if (( rc != 0 )); then
    echo "!!! ${pid_to_tc[$pid]} FAILED (exit code ${rc})"
    echo "    Command: ${pid_to_cmd[$pid]}"
    overall_rc=1
  else
    echo "--- ${pid_to_tc[$pid]} PASSED"
  fi
  # Remove finished PID from pids array and maps
  # New array needed to avoid holes in existing array
  local new_pids=()
  for p in "${pids[@]}"; do
    if [[ "$p" != "$pid" ]]; then
      new_pids+=("$p")
    fi
  done
  # Replace existing array with the new array
  pids=("${new_pids[@]}")
  unset pid_to_cmd["$pid"]
  unset pid_to_tc["$pid"]
  ((running--))
}

# Function to wait for any job to finish and process it
wait_for_any_and_report() {
  wait -n  # Wait for any job to finish
  for finished_pid in "${pids[@]}"; do
    if ! kill -0 "$finished_pid" 2>/dev/null; then
      wait_and_report "$finished_pid"
      break
    fi
  done
}

total_tests=${#tests[@]}

for entry in "${tests[@]}"; do
  tc="${entry%%:*}"
  to="${entry##*:}"

  ((kicked_off++))
  remaining=$((total_tests - kicked_off))

  echo
  echo "=== Running ${tc} (timeout ${to}) ==="
  echo "Tests kicked off: $kicked_off, Remaining: $remaining"

  # 3) build a fresh arg array
  args=( --interactive
         --name css_regress
         --project Caliptra ss_build
         -tc "${tc}"
         "${cov_args[@]}"
         -op
         -sb
         -to "${to}"
  )

  # optional: echo the exact command line to debug
  echo "+ submit ${args[*]}"

  # 4) submit tests
  submit "${args[@]}" &
  pid=$!
  pid_to_cmd[$pid]="submit ${args[*]}"
  pid_to_tc[$pid]="${tc}"
  pids+=($pid)
  ((running++))

  # Limit parallel jobs
  if (( running >= max_parallel )); then
    echo "Reached max parallel jobs ($max_parallel). Waiting for one to complete..."
    wait_for_any_and_report
  fi
done

echo "All tests have been kicked off. Waiting for remaining tests to finish."

# 5) Wait for all remaining jobs to finish and process them
while ((${#pids[@]} > 0)); do
  wait_for_any_and_report
done

echo
if (( overall_rc != 0 )); then
  echo "One or more tests failed."
else
  echo "All tests passed."
fi

exit $overall_rc
