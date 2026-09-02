# SPDX-License-Identifier: Apache-2.0
# 
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

export CALIPTRA_ROOT="${CALIPTRA_ROOT:-$CALIPTRA_SS_ROOT/third_party/caliptra-rtl}"

# The register generator itself is project-agnostic and lives in the
# caliptra-rtl submodule; caliptra-ss supplies its own source RDLs, output
# locations, and (from the submodule) the Jinja2 templates for the UVM output.
REG_GEN_PY=$CALIPTRA_ROOT/tools/scripts/reg_gen.py
UVM_TPL=$CALIPTRA_ROOT/tools/templates/rdl/uvm

REG_GEN="python3 $REG_GEN_PY --uvm-template-dir $UVM_TPL"

# MCI block: regblock SystemVerilog -> src/mci/rtl/generated,
#            UVM RAL model          -> src/mci/dv/generated
$REG_GEN $CALIPTRA_SS_ROOT/src/mci/rdl/mci_reg.rdl                       \
    --emit-rtl --rtl-output $CALIPTRA_SS_ROOT/src/mci/rtl/generated      \
    --emit-dv  --dv-output  $CALIPTRA_SS_ROOT/src/mci/dv/generated

$REG_GEN $CALIPTRA_SS_ROOT/src/mci/rdl/mcu_mbox_csr.rdl                  \
    --emit-rtl --rtl-output $CALIPTRA_SS_ROOT/src/mci/rtl/generated      \
    --emit-dv  --dv-output  $CALIPTRA_SS_ROOT/src/mci/dv/generated

$REG_GEN $CALIPTRA_SS_ROOT/src/mci/rdl/trace_buffer_csr.rdl             \
    --emit-rtl --rtl-output $CALIPTRA_SS_ROOT/src/mci/rtl/generated      \
    --emit-dv  --dv-output  $CALIPTRA_SS_ROOT/src/mci/dv/generated
