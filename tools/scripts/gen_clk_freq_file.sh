#!/usr/bin/env bash
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

# This script generates or validates a clock frequency and saves it to a file for the Caliptra SS
# The script will be run in the Caliptra SS workspace

save_frequency() {
    # Check if the provided path is a valid directory
    if [ ! -d "$1" ]; then
        echo "Error: The provided path is not a valid directory."
        return 1
    fi

    # Define the array of supported frequencies
    # frequencies=(160 400 1000)
    #-- FIXME: At Lower Frequencies I3C is not able to capture the Dynamic Address assignment.
    frequencies=(1000)

    # If $2 is provided, validate it; otherwise, select a random frequency
    if [ -n "$2" ]; then
        input_frequency=$2
        if [[ ! " ${frequencies[@]} " =~ " ${input_frequency} " ]]; then
            echo "Error: The provided frequency ($input_frequency MHz) is not supported."
            echo "Supported frequencies are: ${frequencies[*]}"
            return 1
        fi
        selected_frequency=$input_frequency
    else
        # Randomly select an index from the array
        random_index=$((RANDOM % ${#frequencies[@]}))
        selected_frequency=${frequencies[$random_index]}
    fi

    # Save the selected frequency to the specified file
    echo "$selected_frequency" > "$1/caliptra_ss_clk_freq.cfg"
    echo "#define CALIPTRA_SS_CLK_FREQ $selected_frequency" > "$1/caliptra_ss_clk_freq.h"

    # Print the selected frequency
    echo "Caliptra subsystem simulation clock freq set to $selected_frequency MHz"
}

# Call the function with the directory path and optional frequency as arguments
save_frequency "$1" "$2"
