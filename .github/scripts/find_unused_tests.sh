#!/bin/bash

################################################################################
# Script to find unused test directories in Caliptra-SS integration tests.
#
# A test is considered "used" if:
# 1. It appears directly in caliptra_ss_master_test_list.csv
# 2. It appears directly in L1_JTAG_caliptra_ss_top_tb_regression.csv
# 3. It's referenced in a .yml file of another test that IS used (transitive)
# 4. It's listed in the waiver file with a valid justification
#
# Usage:
#   find_unused_tests.sh [OPTIONS] [CALIPTRA_SS_ROOT]
#
# Options:
#   -h, --help    Show help message and exit
#
# Arguments:
#   CALIPTRA_SS_ROOT: Path to the Caliptra-SS root directory (optional)
#                     If not provided, uses $CALIPTRA_SS_ROOT environment variable
#                     or $GITHUB_WORKSPACE if running in GitHub Actions
#
# Exit Codes:
#   0 - Success: All tests are used or properly waived
#   1 - Failure: Unused tests found or waivers missing justification
################################################################################

set -u  # Exit on undefined variables

# Function to show help
show_help() {
    cat << 'EOF'
Unused Tests Check - Find unused test directories in Caliptra-SS

USAGE:
    find_unused_tests.sh [OPTIONS] [CALIPTRA_SS_ROOT]

OPTIONS:
    -h, --help              Show this help message and exit

ARGUMENTS:
    CALIPTRA_SS_ROOT        Path to Caliptra-SS root directory (optional)
                            If not provided, uses $CALIPTRA_SS_ROOT or $GITHUB_WORKSPACE

DESCRIPTION:
    This script checks that all test directories under src/integration/test_suites/
    are being used. Tests are considered "used" if they:
    
    1. Appear in CSV files under src/integration/stimulus/
    2. Are referenced in .yml files of other tests (transitive)
    3. Are listed in the waiver file with justification

    The script will fail if:
    - Any test directory is unused and not waived
    - Any waiver entry lacks a justification comment

WAIVER FILE:
    Location: .github/workflow_metadata/unused_tests_waiver.txt
    Format:   test_directory_name # Comment explaining why excluded
    
    Example:
        deprecated_test # Scheduled for removal Q1 2025
        wip_feature # Under development, not ready for CI

EXIT CODES:
    0 - All tests are used or properly waived
    1 - Unused tests found or waivers missing justification

EXAMPLES:
    # Use environment variable
    export CALIPTRA_SS_ROOT=/path/to/caliptra-ss
    find_unused_tests.sh
    
    # Specify path directly
    find_unused_tests.sh /path/to/caliptra-ss
    
    # Show help
    find_unused_tests.sh --help

EOF
    exit 0
}

# Parse command line arguments
if [ $# -ge 1 ] && { [ "$1" = "-h" ] || [ "$1" = "--help" ]; }; then
    show_help
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
    echo "Usage: $0 [CALIPTRA_SS_ROOT]" >&2
    echo "Run '$0 --help' for more information" >&2
    exit 1
fi

# Define paths relative to CALIPTRA_SS_ROOT
TEST_SUITES_PATH="$CALIPTRA_SS_ROOT/src/integration/test_suites"
MASTER_CSV="$CALIPTRA_SS_ROOT/src/integration/stimulus/testsuites/caliptra_ss_master_test_list.csv"
JTAG_CSV="$CALIPTRA_SS_ROOT/src/integration/stimulus/L1_JTAG_caliptra_ss_top_tb_regression.csv"
STIMULUS_DIR="$CALIPTRA_SS_ROOT/src/integration/stimulus"
WAIVER_FILE="$CALIPTRA_SS_ROOT/.github/workflow_metadata/unused_tests_waiver.txt"

# Arrays to store results
declare -a ALL_TESTS
declare -a DIRECTLY_USED
declare -a TRANSITIVELY_USED
declare -a WAIVED_TESTS
declare -a WAIVED_NO_JUSTIFICATION
declare -a WAIVED_INVALID
declare -a WAIVED_UNNECESSARY
declare -a UNUSED_TESTS

# Associative array for faster lookups
declare -A USED_TESTS_MAP
declare -A CHECKED_TESTS_MAP
declare -A ALL_TESTS_MAP

# Exit code: 0 if no unused tests, 1 if unused tests found
EXIT_CODE=0

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

################################################################################
# Function to print section headers
################################################################################
print_header() {
    echo ""
    echo "================================================================================"
    echo "$1"
    echo "================================================================================"
    echo ""
}

################################################################################
# Step 1: Get all test directories (excluding 'lib', 'libs', and 'includes')
################################################################################
get_all_tests() {
    print_header "Step 1: Scanning test directories"
    
    if [ ! -d "$TEST_SUITES_PATH" ]; then
        echo -e "${RED}Error: Test suites path does not exist: $TEST_SUITES_PATH${NC}" >&2
        exit 1
    fi
    
    echo "Scanning: $TEST_SUITES_PATH"
    
    # Get all directories excluding 'lib', 'libs', and 'includes'
    while IFS= read -r dir; do
        local basename=$(basename "$dir")
        if [ "$basename" != "lib" ] && [ "$basename" != "libs" ] && [ "$basename" != "includes" ]; then
            ALL_TESTS+=("$basename")
            ALL_TESTS_MAP[$basename]=1
        fi
    done < <(find "$TEST_SUITES_PATH" -maxdepth 1 -type d ! -name "test_suites" | sort)
    
    echo -e "${GREEN}Found ${#ALL_TESTS[@]} test directories (excluding 'lib', 'libs', and 'includes')${NC}"
}

################################################################################
# Step 2: Get directly used tests from CSV files
################################################################################
get_directly_used_tests() {
    print_header "Step 2: Finding directly referenced tests in CSV files"
    
    local -A seen_tests
    
    # Search in master CSV file
    if [ -f "$MASTER_CSV" ]; then
        echo "Searching in: $MASTER_CSV"
        local count=0
        
        # Look for test_suites/<test_name> pattern
        while IFS= read -r test; do
            if [ -n "$test" ] && [ -z "${seen_tests[$test]:-}" ]; then
                DIRECTLY_USED+=("$test")
                seen_tests[$test]=1
                USED_TESTS_MAP[$test]=1
            fi
        done < <(grep -oP 'test_suites/\K[^/,\s]+' "$MASTER_CSV" 2>/dev/null | sort -u)
        
        # Also check bare test names in first column
        while IFS= read -r test; do
            if [ -n "$test" ] && [ "$test" != "TestName" ] && [ -z "${seen_tests[$test]:-}" ]; then
                DIRECTLY_USED+=("$test")
                seen_tests[$test]=1
                USED_TESTS_MAP[$test]=1
            fi
        done < <(grep -v '^#' "$MASTER_CSV" 2>/dev/null | tail -n +2 | cut -d',' -f1 | sed 's/^[[:space:]]*//;s/[[:space:]]*$//' | grep -v '^$' | sort -u)
        
        count=$(grep -c 'test_suites/' "$MASTER_CSV" 2>/dev/null || echo 0)
        echo "  - Found $count test_suites/ references in caliptra_ss_master_test_list.csv"
    else
        echo -e "${YELLOW}Warning: Master CSV not found: $MASTER_CSV${NC}" >&2
    fi
    
    # Search in JTAG CSV file
    if [ -f "$JTAG_CSV" ]; then
        echo "Searching in: $JTAG_CSV"
        
        # Look for test_suites/<test_name> pattern
        while IFS= read -r test; do
            if [ -n "$test" ] && [ -z "${seen_tests[$test]:-}" ]; then
                DIRECTLY_USED+=("$test")
                seen_tests[$test]=1
                USED_TESTS_MAP[$test]=1
            fi
        done < <(grep -oP 'test_suites/\K[^/,\s]+' "$JTAG_CSV" 2>/dev/null | sort -u)
        
        # Also look for bare test names
        while IFS= read -r test; do
            if [ -n "$test" ] && [ "$test" != "Test Name" ] && [ -z "${seen_tests[$test]:-}" ]; then
                DIRECTLY_USED+=("$test")
                seen_tests[$test]=1
                USED_TESTS_MAP[$test]=1
            fi
        done < <(grep -v '^#' "$JTAG_CSV" 2>/dev/null | tail -n +2 | cut -d',' -f1 | sed 's/^[[:space:]]*//;s/[[:space:]]*$//' | grep -v '^$' | grep -v '^Test Name' | sort -u)
        
        local count=$(grep -v '^#' "$JTAG_CSV" 2>/dev/null | tail -n +2 | wc -l)
        echo "  - Found $count test entries in L1_JTAG_caliptra_ss_top_tb_regression.csv"
    else
        echo -e "${YELLOW}Warning: JTAG CSV not found: $JTAG_CSV${NC}" >&2
    fi
    
    # Search all CSV files in stimulus directory
    if [ -d "$STIMULUS_DIR" ]; then
        echo "Searching all CSV files in stimulus directory..."
        while IFS= read -r test; do
            if [ -n "$test" ] && [ -z "${seen_tests[$test]:-}" ]; then
                DIRECTLY_USED+=("$test")
                seen_tests[$test]=1
                USED_TESTS_MAP[$test]=1
            fi
        done < <(find "$STIMULUS_DIR" -name "*.csv" -type f -exec grep -oP 'test_suites/\K[^/,\s]+' {} \; 2>/dev/null | sort -u)
    fi
    
    # Filter to only tests that actually exist
    local -a filtered
    for test in "${DIRECTLY_USED[@]}"; do
        for actual_test in "${ALL_TESTS[@]}"; do
            if [ "$test" = "$actual_test" ]; then
                filtered+=("$test")
                break
            fi
        done
    done
    DIRECTLY_USED=("${filtered[@]}")
    
    echo -e "${GREEN}Total directly used tests: ${#DIRECTLY_USED[@]}${NC}"
}

################################################################################
# Step 3: Find transitive dependencies (tests referenced in .yml files)
################################################################################
find_transitive_dependencies() {
    print_header "Step 3: Finding transitive dependencies"
    
    echo "Analyzing .yml files for TEST_DIR references..."
    
    local -a to_check=("${DIRECTLY_USED[@]}")
    
    while [ ${#to_check[@]} -gt 0 ]; do
        local current_test="${to_check[0]}"
        to_check=("${to_check[@]:1}")
        
        # Skip if already checked
        [ -n "${CHECKED_TESTS_MAP[$current_test]:-}" ] && continue
        CHECKED_TESTS_MAP[$current_test]=1
        
        # Find .yml files in this test directory
        local test_dir="$TEST_SUITES_PATH/$current_test"
        [ ! -d "$test_dir" ] && continue
        
        # Look for TEST_DIR references
        while IFS= read -r dep; do
            if [ -n "$dep" ] && [ -z "${USED_TESTS_MAP[$dep]:-}" ]; then
                # Check if dep exists in ALL_TESTS
                for actual_test in "${ALL_TESTS[@]}"; do
                    if [ "$dep" = "$actual_test" ]; then
                        TRANSITIVELY_USED+=("$dep")
                        USED_TESTS_MAP[$dep]=1
                        to_check+=("$dep")
                        echo "  Found dependency: $current_test -> $dep"
                        break
                    fi
                done
            fi
        done < <(find "$test_dir" -name "*.yml" -type f -exec grep -oP 'TEST_DIR=\$CALIPTRA_SS_ROOT/src/integration/test_suites/\K[^/\s\n]+' {} \; 2>/dev/null)
    done
    
    echo -e "${GREEN}Found ${#TRANSITIVELY_USED[@]} transitively used tests${NC}"
}

################################################################################
# Function to read waived tests from waiver file
################################################################################
get_waived_tests() {
    print_header "Reading waiver file"
    
    # Ensure arrays are initialized (even if empty)
    WAIVED_TESTS=()
    WAIVED_NO_JUSTIFICATION=()
    WAIVED_INVALID=()
    
    if [ ! -f "$WAIVER_FILE" ]; then
        echo "No waiver file found at: $WAIVER_FILE"
        echo "All tests must be used or added to waiver file."
        return
    fi
    
    echo "Reading waiver file: $WAIVER_FILE"
    
    local waived_count=0
    while IFS= read -r line; do
        # Skip empty lines
        [[ -z "$line" ]] && continue
        
        # Skip comment lines (lines starting with #)
        [[ "$line" =~ ^[[:space:]]*# ]] && continue
        
        # Extract test name (everything before the first # or end of line)
        local test_name=$(echo "$line" | sed 's/#.*//' | xargs)
        
        # Skip if test name is empty after processing
        [[ -z "$test_name" ]] && continue
        
        # Extract comment if present
        local comment=""
        if [[ "$line" =~ "#" ]]; then
            comment=$(echo "$line" | sed 's/^[^#]*#//' | xargs)
        fi
        
        # Check if test exists in ALL_TESTS
        if [ -z "${ALL_TESTS_MAP[$test_name]:-}" ]; then
            echo -e "  - ${RED}$test_name (ERROR: test directory does not exist)${NC}" >&2
            WAIVED_INVALID+=("$test_name")
            EXIT_CODE=1
            continue
        fi
        
        WAIVED_TESTS+=("$test_name")
        USED_TESTS_MAP[$test_name]=1
        waived_count=$((waived_count + 1))
        
        if [ -n "$comment" ]; then
            echo "  - $test_name (waived: $comment)"
        else
            echo -e "  - ${RED}$test_name (ERROR: missing justification)${NC}" >&2
            WAIVED_NO_JUSTIFICATION+=("$test_name")
            EXIT_CODE=1
        fi
    done < "$WAIVER_FILE"
    
    echo -e "${GREEN}Found $waived_count valid waived tests${NC}"
    
    if [ ${#WAIVED_NO_JUSTIFICATION[@]} -gt 0 ] 2>/dev/null; then
        echo -e "${RED}ERROR: ${#WAIVED_NO_JUSTIFICATION[@]} waived test(s) lack justification comments${NC}" >&2
    fi
    
    if [ ${#WAIVED_INVALID[@]} -gt 0 ] 2>/dev/null; then
        echo -e "${RED}ERROR: ${#WAIVED_INVALID[@]} waived test(s) do not exist${NC}" >&2
    fi
}

################################################################################
# Step 4: Check for unnecessary waivers
################################################################################
check_unnecessary_waivers() {
    print_header "Step 4: Checking for unnecessary waivers"
    
    # Ensure array is initialized
    WAIVED_UNNECESSARY=()
    
    # Check each waived test to see if it's actually being used
    for test in "${WAIVED_TESTS[@]}"; do
        # Check if test is in directly used
        for used in "${DIRECTLY_USED[@]}"; do
            if [ "$test" = "$used" ]; then
                echo -e "  ${YELLOW}WARNING: $test is waived but also used directly in CSV${NC}" >&2
                WAIVED_UNNECESSARY+=("$test")
                EXIT_CODE=1
                break
            fi
        done
        
        # Check if test is in transitively used
        for used in "${TRANSITIVELY_USED[@]}"; do
            if [ "$test" = "$used" ]; then
                echo -e "  ${YELLOW}WARNING: $test is waived but also used transitively${NC}" >&2
                WAIVED_UNNECESSARY+=("$test")
                EXIT_CODE=1
                break
            fi
        done
    done
    
    if [ ${#WAIVED_UNNECESSARY[@]} -eq 0 ]; then
        echo -e "${GREEN}No unnecessary waivers found${NC}"
    else
        echo -e "${RED}Found ${#WAIVED_UNNECESSARY[@]} unnecessary waiver(s)${NC}" >&2
    fi
}

################################################################################
# Step 5: Calculate unused tests
################################################################################
calculate_unused_tests() {
    print_header "Step 4: Calculating unused tests"
    
    # Find tests that are not in the USED_TESTS_MAP
    for test in "${ALL_TESTS[@]}"; do
        if [ -z "${USED_TESTS_MAP[$test]:-}" ]; then
            UNUSED_TESTS+=("$test")
        fi
    done
    
    local total=${#ALL_TESTS[@]}
    # Set default; check if variable is defined && set directly to length of env var exists
    local directly=0; [ -n "${DIRECTLY_USED+x}" ] && directly=${#DIRECTLY_USED[@]}
    local transitively=0; [ -n "${TRANSITIVELY_USED+x}" ] && transitively=${#TRANSITIVELY_USED[@]}
    local waived=0; [ -n "${WAIVED_TESTS+x}" ] && waived=${#WAIVED_TESTS[@]}
    local all_used=$((directly + transitively + waived))
    local unused=0; [ -n "${UNUSED_TESTS+x}" ] && unused=${#UNUSED_TESTS[@]}
    
    echo "Total test directories: $total"
    echo "Used tests (directly): $directly"
    echo "Used tests (transitively): $transitively"
    echo "Waived tests: $waived"
    echo "Total used tests: $all_used"
    echo -e "${RED}UNUSED tests: $unused${NC}"
    
    # Set exit code if there are unused tests
    if [ $unused -gt 0 ]; then
        EXIT_CODE=1
    fi
}

################################################################################
# Step 5: Display results
################################################################################
display_results() {
    print_header "RESULTS"
    
    local total=${#ALL_TESTS[@]}
    # Set default; check if variable is defined && set directly to length of env var exists
    local directly=0; [ -n "${DIRECTLY_USED+x}" ] && directly=${#DIRECTLY_USED[@]}
    local transitively=0; [ -n "${TRANSITIVELY_USED+x}" ] && transitively=${#TRANSITIVELY_USED[@]}
    local waived=0; [ -n "${WAIVED_TESTS+x}" ] && waived=${#WAIVED_TESTS[@]}
    local all_used=$((directly + transitively + waived))
    local unused=0; [ -n "${UNUSED_TESTS+x}" ] && unused=${#UNUSED_TESTS[@]}
    local waived_no_justification=0
    local waived_invalid=0
    local waived_unnecessary=0
    
    if [ ${#WAIVED_NO_JUSTIFICATION[@]} -gt 0 ] 2>/dev/null; then
        waived_no_justification=${#WAIVED_NO_JUSTIFICATION[@]}
    fi
    if [ ${#WAIVED_INVALID[@]} -gt 0 ] 2>/dev/null; then
        waived_invalid=${#WAIVED_INVALID[@]}
    fi
    if [ ${#WAIVED_UNNECESSARY[@]} -gt 0 ] 2>/dev/null; then
        waived_unnecessary=${#WAIVED_UNNECESSARY[@]}
    fi
    
    echo "Total test directories: $total"
    echo "Used tests (directly): $directly"
    echo "Used tests (transitively): $transitively"
    echo "Waived tests: $waived"
    echo "Total used tests: $all_used"
    echo ""
    
    # Report unused tests
    if [ $unused -gt 0 ]; then
        echo -e "${RED}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
        echo -e "${RED}✗ UNUSED TESTS FOUND: $unused test(s) are not being used${NC}"
        echo -e "${RED}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
        echo ""
        for test in "${UNUSED_TESTS[@]+"${UNUSED_TESTS[@]}"}"; do
            echo -e "  ${RED}✗${NC} $test"
        done
        echo ""
        echo -e "${YELLOW}These tests must either be:${NC}"
        echo "  1. Added to a test suite CSV file, or"
        echo "  2. Referenced in another test's .yml file, or"
        echo "  3. Added to the waiver file with justification: $WAIVER_FILE"
        echo ""
    fi
    
    # Report waivers without justification
    if [ $waived_no_justification -gt 0 ]; then
        echo -e "${RED}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
        echo -e "${RED}✗ WAIVERS MISSING JUSTIFICATION: $waived_no_justification waiver(s) lack comments${NC}"
        echo -e "${RED}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
        echo ""
        for test in "${WAIVED_NO_JUSTIFICATION[@]}"; do
            echo -e "  ${RED}✗${NC} $test"
        done
        echo ""
        echo -e "${YELLOW}Waiver file format:${NC}"
        echo "  test_directory_name # Comment explaining why this test is excluded"
        echo ""
    fi
    
    # Report invalid waivers (test directory doesn't exist)
    if [ $waived_invalid -gt 0 ]; then
        echo -e "${RED}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
        echo -e "${RED}✗ INVALID WAIVERS: $waived_invalid waiver(s) reference non-existent tests${NC}"
        echo -e "${RED}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
        echo ""
        for test in "${WAIVED_INVALID[@]}"; do
            echo -e "  ${RED}✗${NC} $test (test directory does not exist)"
        done
        echo ""
        echo -e "${YELLOW}These waivers reference tests that don't exist in:${NC}"
        echo "  $TEST_SUITES_PATH"
        echo ""
    fi
    
    # Report unnecessary waivers (test is already used)
    if [ $waived_unnecessary -gt 0 ]; then
        echo -e "${YELLOW}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
        echo -e "${YELLOW}✗ UNNECESSARY WAIVERS: $waived_unnecessary waiver(s) for already-used tests${NC}"
        echo -e "${YELLOW}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
        echo ""
        for test in "${WAIVED_UNNECESSARY[@]}"; do
            echo -e "  ${YELLOW}✗${NC} $test (already used in CSV or transitively)"
        done
        echo ""
        echo -e "${YELLOW}These tests are already being used and don't need waivers.${NC}"
        echo "Remove them from: $WAIVER_FILE"
        echo ""
    fi
    
    # Final status
    if [ $EXIT_CODE -eq 0 ]; then
        echo -e "${GREEN}════════════════════════════════════════════════════════════════════════════════${NC}"
        echo -e "${GREEN}✓✓✓ CHECK PASSED ✓✓✓${NC}"
        echo -e "${GREEN}All tests are used or properly waived${NC}"
        echo -e "${GREEN}════════════════════════════════════════════════════════════════════════════════${NC}"
        echo ""
        echo "Exit code: 0"
    else
        echo -e "${RED}════════════════════════════════════════════════════════════════════════════════${NC}"
        echo -e "${RED}✗✗✗ CHECK FAILED ✗✗✗${NC}"
        
        local error_count=0
        local error_msg=""
        
        if [ $unused -gt 0 ]; then
            error_msg="${error_msg}$unused unused test(s)"
            error_count=$((error_count + 1))
        fi
        if [ $waived_no_justification -gt 0 ]; then
            [ -n "$error_msg" ] && error_msg="${error_msg}, "
            error_msg="${error_msg}$waived_no_justification waiver(s) without justification"
            error_count=$((error_count + 1))
        fi
        if [ $waived_invalid -gt 0 ]; then
            [ -n "$error_msg" ] && error_msg="${error_msg}, "
            error_msg="${error_msg}$waived_invalid invalid waiver(s)"
            error_count=$((error_count + 1))
        fi
        if [ $waived_unnecessary -gt 0 ]; then
            [ -n "$error_msg" ] && error_msg="${error_msg}, "
            error_msg="${error_msg}$waived_unnecessary unnecessary waiver(s)"
            error_count=$((error_count + 1))
        fi
        
        echo -e "${RED}Found: $error_msg${NC}"
        echo -e "${RED}════════════════════════════════════════════════════════════════════════════════${NC}"
        echo ""
        echo "Exit code: 1" >&2
    fi
    
    echo ""
}

################################################################################
# Main execution
################################################################################
main() {
    print_header "Caliptra-SS Unused Test Finder"
    
    echo "Caliptra-SS Root: $CALIPTRA_SS_ROOT"
    
    get_all_tests
    get_directly_used_tests
    find_transitive_dependencies
    get_waived_tests
    check_unnecessary_waivers
    calculate_unused_tests
    display_results
    
    exit $EXIT_CODE
}

# Run main function
main
