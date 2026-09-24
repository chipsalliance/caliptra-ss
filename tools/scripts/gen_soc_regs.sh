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

# Check if a path is provided as an argument
if [ -z "$1" ]; then
    # No argument provided, use the default CALIPTRA_SS_ROOT
    SCRIPT_PATH="$CALIPTRA_SS_ROOT"
else
    # Use the provided argument as the path
    SCRIPT_PATH="$1"
fi

# Argument to clobber the generated docs folder (for just rebuilding header files)
clobber_docs=0;
if [[ -n "${2:+empty}" && "$2" == "--no-docs" ]]; then
    clobber_docs=1;
fi

# Check if CALIPTRA_SS_ROOT is set if no argument is provided
if [ -z "$SCRIPT_PATH" ]; then
    echo "Error, must set CALIPTRA_SS_ROOT or provide a path as an argument"
    exit 1
fi

# Run the Python script with the appropriate paths
python3 ${SCRIPT_PATH}/third_party/caliptra-rtl/tools/scripts/reg_doc_gen.py \
${SCRIPT_PATH}/src/integration/rtl/soc_address_map.rdl

if [[ $clobber_docs -eq 1 ]]; then
    echo "Clobber generated 'docs'"
    rm -r ${SCRIPT_PATH}/src/integration/docs
fi
