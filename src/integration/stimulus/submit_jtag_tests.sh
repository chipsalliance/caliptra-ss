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


set -euo pipefail

submit --interactive --name css_regress --project Caliptra ss_build -tc smoke_test_jtag_uds_prog        -op -sb -to 220000
submit --interactive --name css_regress --project Caliptra ss_build -tc smoke_test_jtag_manuf_dbg       -op -sb -to 220000
submit --interactive --name css_regress --project Caliptra ss_build -tc smoke_test_jtag_prod_dbg          -op -sb -to 10000000
submit --interactive --name css_regress --project Caliptra ss_build -tc caliptra_ss_jtag_lcc_st_trans     -op -sb -to 85000
submit --interactive --name css_regress --project Caliptra ss_build -tc smoke_test_jtag_lcc_registers     -op -sb -to 85000