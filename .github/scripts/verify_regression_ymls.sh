#!/bin/bash
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

set -e

show_help() {
    cat << EOF
Usage: $(basename "$0") [CALIPTRA_SS_ROOT]

Verify that regression YAML files are in sync with the generation script.

This script:
  1. Backs up current regression YAML files
  2. Runs the generation script (gen_caliptra_ss_regression_ymls.py)
  3. Compares the generated files with the originals
  4. Fails if any differences are found

Arguments:
  CALIPTRA_SS_ROOT    Path to the Caliptra SS root directory (optional)
                      If not provided, uses \$CALIPTRA_SS_ROOT environment variable
                      or \$GITHUB_WORKSPACE in CI environment

Options:
  -h, --help          Show this help message and exit

Examples:
  # Run from anywhere with explicit path
  $(basename "$0") /path/to/caliptra-ss

  # Run with CALIPTRA_SS_ROOT environment variable set
  export CALIPTRA_SS_ROOT=/path/to/caliptra-ss
  $(basename "$0")

  # Run from within the repository (auto-detect)
  cd /path/to/caliptra-ss
  $(basename "$0")

Exit codes:
  0    Success - YAML files are in sync
  1    Failure - YAML files differ from generated output

EOF
}

# Parse command line arguments
if [ $# -ge 1 ] && { [ "$1" = "-h" ] || [ "$1" = "--help" ]; }; then
    show_help
    exit 0
fi

# Determine CALIPTRA_SS_ROOT
if [ $# -ge 1 ] && [ "$1" != "-h" ] && [ "$1" != "--help" ]; then
    CALIPTRA_SS_ROOT="$1"
elif [ -n "${CALIPTRA_SS_ROOT:-}" ]; then
    CALIPTRA_SS_ROOT="$CALIPTRA_SS_ROOT"
elif [ -n "${GITHUB_WORKSPACE:-}" ]; then
    CALIPTRA_SS_ROOT="$GITHUB_WORKSPACE"
else
    echo "Error: CALIPTRA_SS_ROOT not specified and not set as environment variable" >&2
    show_help
    exit 1
fi

# Validate CALIPTRA_SS_ROOT exists
if [ ! -d "$CALIPTRA_SS_ROOT" ]; then
    echo "Error: Directory does not exist: $CALIPTRA_SS_ROOT" >&2
    exit 1
fi

STIMULUS_DIR="$CALIPTRA_SS_ROOT/src/integration/stimulus"
GEN_SCRIPT="$CALIPTRA_SS_ROOT/tools/scripts/gen_caliptra_ss_regression_ymls.py"

# Validate required paths exist
if [ ! -d "$STIMULUS_DIR" ]; then
    echo "Error: Stimulus directory not found: $STIMULUS_DIR" >&2
    exit 1
fi

if [ ! -f "$GEN_SCRIPT" ]; then
    echo "Error: Generation script not found: $GEN_SCRIPT" >&2
    exit 1
fi

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "=================================================="
echo "Regression YAML Verification"
echo "=================================================="
echo "CALIPTRA_SS_ROOT: $CALIPTRA_SS_ROOT"
echo "Stimulus Dir:     $STIMULUS_DIR"
echo "Generation Script: $GEN_SCRIPT"
echo ""

# Create a temporary directory
TEMP_DIR=$(mktemp -d)
trap "rm -rf $TEMP_DIR" EXIT

# Copy current YAML files to temp directory for comparison
echo "Backing up current YAML files..."
cp "$STIMULUS_DIR"/*.yml "$TEMP_DIR/" 2>/dev/null || {
    echo -e "${RED}ERROR: No YAML files found in $STIMULUS_DIR${NC}"
    exit 1
}

# Run the generation script
echo "Running generation script..."
if ! python3 "$GEN_SCRIPT"; then
    echo -e "${RED}ERROR: Generation script failed${NC}"
    exit 1
fi

echo ""

# Compare files
echo "Checking for changes in YAML files..."
echo "--------------------------------------------------"
DIFF_FOUND=0

for backup_file in "$TEMP_DIR"/*.yml; do
    filename=$(basename "$backup_file")
    current_file="$STIMULUS_DIR/$filename"

    if [ ! -f "$current_file" ]; then
        echo -e "${RED}✗ File removed: $filename${NC}"
        DIFF_FOUND=1
        continue
    fi

    if ! diff -q "$backup_file" "$current_file" > /dev/null; then
        echo -e "${RED}✗ File modified: $filename${NC}"
        echo "  Differences:"
        diff -u "$backup_file" "$current_file" | head -20
        echo ""
        DIFF_FOUND=1
    else
        echo -e "${GREEN}✓ No changes: $filename${NC}"
    fi
done

# Check for newly created files
for current_file in "$STIMULUS_DIR"/*.yml; do
    filename=$(basename "$current_file")
    if [ ! -f "$TEMP_DIR/$filename" ]; then
        echo -e "${RED}✗ New file created: $filename${NC}"
        DIFF_FOUND=1
    fi
done

echo "=================================================="
if [ $DIFF_FOUND -eq 0 ]; then
    echo -e "${GREEN}SUCCESS: All regression YAML files are up-to-date!${NC}"
    exit 0
else
    echo -e "${RED}FAILURE: Regression YAML files are NOT in sync${NC}"
    echo ""
    echo "To fix this issue:"
    echo "  1. Review the changes above"
    echo "  2. Add/remove the appropriate tests in the CSV file:"
    echo "     $STIMULUS_DIR/testsuites/caliptra_ss_master_test_list.csv"
    echo "  3. Run the generation script to update YAML files:"
    echo "     python3 $GEN_SCRIPT"
    echo "  4. Commit both the updated CSV and YAML files"
    exit 1
fi
