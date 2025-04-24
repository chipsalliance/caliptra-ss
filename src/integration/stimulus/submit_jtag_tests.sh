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


set -eo pipefail

if [ -z "${COVERAGE_DIR_PATH}" ]; then
  echo "COVERAGE_DIR_PATH is not defined."
  COV_CMD=""
else
  echo "COVERAGE_DIR_PATH is defined as: ${COVERAGE_DIR_PATH}"
  COV_CMD="-cov_dir ${COVERAGE_DIR_PATH}"
fi

submit --interactive --name css_regress --project Caliptra ss_build -tc smoke_test_jtag_uds_prog      -c ${COV_CMD} -op -sb -to 520000
submit --interactive --name css_regress --project Caliptra ss_build -tc smoke_test_jtag_manuf_dbg     -c ${COV_CMD} -op -sb -to 520000
submit --interactive --name css_regress --project Caliptra ss_build -tc smoke_test_jtag_prod_dbg      -c ${COV_CMD} -op -sb -to 10000000
submit --interactive --name css_regress --project Caliptra ss_build -tc smoke_test_jtag_lcc_registers -c ${COV_CMD} -op -sb -to 185000
submit --interactive --name css_regress --project Caliptra ss_build -tc caliptra_ss_jtag_lcc_st_trans -c ${COV_CMD} -op -sb -to 220000
submit --interactive --name css_regress --project Caliptra ss_build -tc smoke_test_jtag_mcu_bp        -c ${COV_CMD} -op -sb -to 220000
submit --interactive --name css_regress --project Caliptra ss_build -tc smoke_test_jtag_mcu_intent    -c ${COV_CMD} -op -sb -to 220000
#assertion fails in lcc state translator - put back after fixed
#submit --interactive --name css_regress --project Caliptra ss_build -tc smoke_test_jtag_mcu_unlock    -c ${COV_CMD} -op -sb -to 220000