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

for entry in "${tests[@]}"; do
  tc="${entry%%:*}"
  to="${entry##*:}"

  echo
  echo "=== Running ${tc} (timeout ${to}) ==="

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

  submit "${args[@]}"
  rc=$?
  if (( rc != 0 )); then
    echo "!!! ${tc} FAILED (exit code ${rc})"
    overall_rc=1
  else
    echo "--- ${tc} PASSED"
  fi
done

echo
if (( overall_rc != 0 )); then
  echo "One or more tests failed."
else
  echo "All tests passed."
fi

exit $overall_rc