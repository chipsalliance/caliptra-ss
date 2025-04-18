#!/usr/bin/env bash
set -euo pipefail

submit --interactive --name css_regress --project "Caliptra ss_build" -tc smoke_test_jtag_uds_prog        -op -sb -to 220000
submit --interactive --name css_regress --project "Caliptra ss_build" -tc smoke_test_jtag_manuf_dbg       -op -sb -to 220000
submit --interactive --name css_regress --project Caliptra ss_build -tc smoke_test_jtag_prod_dbg          -op -sb -to 10000000
submit --interactive --name css_regress --project Caliptra ss_build -tc caliptra_ss_jtag_lcc_st_trans     -op -sb -to 85000