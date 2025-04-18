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

set -euo pipefail

if [[ $# -ne 1 ]]; then
    echo "Error, requires branch name argument"
    exit 1
else
    merge_dest=$1
fi

if ! git show-ref --quiet "${merge_dest}"; then
    echo "Could not find ref named [${merge_dest}]"
    exit 1
else
    echo "Evaluating RDL modifications for merge into [${merge_dest}] with ref [$(git show-ref "${merge_dest}")]"
fi

if [[ -z "${CALIPTRA_SS_ROOT:+"empty"}" ]]; then
    echo "Error, must set CALIPTRA_SS_ROOT"
    exit 1
else
    echo "CALIPTRA_SS_ROOT: '${CALIPTRA_SS_ROOT}'"
fi
cd "${CALIPTRA_SS_ROOT}"

# Run the HTML Doc generator script (to update the REG macro header files)
# and the individual reg generator script but then remove the docs directories
# before checking if the script caused any file modifications
bash "${CALIPTRA_SS_ROOT}/tools/scripts/gen_soc_regs.sh" "${CALIPTRA_SS_ROOT}"
rm -rf "${CALIPTRA_SS_ROOT}/src/integration/docs"

# Check for any file changes
if [[ $(git status -s --untracked-files=all --ignored=traditional -- "${CALIPTRA_SS_ROOT}/src/" | wc -l) -gt 0 ]]; then
  echo "Regenerating reg RDL outputs produced some file changes:";
  git status -s --untracked-files=all --ignored=traditional;
  git diff;
  echo "*****************************************";
  echo "Review above changes locally and resubmit pipeline";
  echo "(Hint: Check ${CALIPTRA_SS_ROOT} for the above changes)";
  echo "*****************************************";
  exit 1;
fi
