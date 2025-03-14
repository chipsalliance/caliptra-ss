#!/usr/bin/env python3
"""
This script generates a SystemVerilog access control table from an HJSON configuration file.
It expects the HJSON file to contain a list of entries, each with:
  - lower_addr: string (hex address, e.g., "0x00000000")
  - upper_addr: string (hex address, e.g., "0x00000008")
  - axi_user_id: a string naming the AXI_USER_ID (e.g., "CALIPTRA_AXI_USER_ID0")

Usage:
    python3 fc_access_control_table.py --hjson <path_to_hjson> --sv_out <output_sv_file>
Example:
    python3 fc_access_control_table.py \
       --hjson ../../src/fuse_ctrl/data/access_control_entries.hjson \
       --sv_out ../../src/fuse_ctrl/rtl/fc_access_control_table.sv
"""

import argparse
import hjson
import sys

def parse_args():
    parser = argparse.ArgumentParser(
        description="Generate a SystemVerilog access control table from an HJSON file."
    )
    parser.add_argument(
        "--hjson", required=True,
        help="Path to the HJSON file containing access control entries."
    )
    parser.add_argument(
        "--sv_out", default="access_control_table.sv",
        help="Output SystemVerilog file name (default: access_control_table.sv)"
    )
    return parser.parse_args()

def load_entries(hjson_file):
    try:
        with open(hjson_file, "r") as f:
            data = hjson.load(f)
    except Exception as e:
        sys.exit(f"Error reading HJSON file {hjson_file}: {e}")
    
    if isinstance(data, dict):
        if "access_control_entries" in data:
            entries = data["access_control_entries"]
        else:
            sys.exit("Error: Expected key 'access_control_entries' in the HJSON file.")
    elif isinstance(data, list):
        entries = data
    else:
        sys.exit("Error: Unexpected HJSON file format. Must be a list or a dict with key 'access_control_entries'.")
    
    return entries

def generate_sv(entries):
    num_entries = len(entries)
    
    # License header and include guard
    license_header = (
        "// SPDX-License-Identifier: Apache-2.0\n"
        "//\n"
        "// Licensed under the Apache License, Version 2.0 (the \"License\");\n"
        "// you may not use this file except in compliance with the License.\n"
        "// You may obtain a copy of the License at\n"
        "//\n"
        "//     http://www.apache.org/licenses/LICENSE-2.0\n"
        "//\n"
        "// Unless required by applicable law or agreed to in writing, software\n"
        "// distributed under the License is distributed on an \"AS IS\" BASIS,\n"
        "// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.\n"
        "// See the License for the specific language governing permissions and\n"
        "// limitations under the License.\n"
        "//\n"
        "`ifndef FC_ACCESS_CONTROL_TABLE_SV\n"
        "`define FC_ACCESS_CONTROL_TABLE_SV\n\n"
    )
    
    # Table definition header
    table_header = (
        "`include \"caliptra_ss_includes.svh\"\n"
        "//------------------------------------------------------------------------------\n"
        "// Generated access control table\n"
        "// DO NOT EDIT: This file is generated by fc_access_control_table.py\n"
        "//------------------------------------------------------------------------------\n\n"
        "typedef struct packed {\n"
        "  logic [31:0] lower_addr;  // Lower bound of the address range\n"
        "  logic [31:0] upper_addr;  // Upper bound of the address range\n"
        "  logic [31:0]  axi_user_id; // AXI user ID allowed to write\n"
        "} access_control_entry_t;\n\n"
        "localparam int FC_TABLE_NUM_RANGES = %d;\n\n" % num_entries +
        "localparam access_control_entry_t access_control_table [FC_TABLE_NUM_RANGES] = '{\n"
    )
    
    # Build the table entries from the HJSON data.
    entries_sv = []
    for idx, entry in enumerate(entries):
        lower = entry.get("lower_addr")
        upper = entry.get("upper_addr")
        axi_user_id = entry.get("axi_user_id")
        
        if lower is None or upper is None or axi_user_id is None:
            sys.exit(f"Error: Entry {idx} is missing one of the required keys: lower_addr, upper_addr, or axi_user_id.")
        
        # Format addresses: remove "0x" if present and pad to 8 hex digits.
        if isinstance(lower, str) and lower.startswith("0x"):
            lower_val = lower[2:].zfill(8)
        else:
            lower_val = str(lower).zfill(8)
        
        if isinstance(upper, str) and upper.startswith("0x"):
            upper_val = upper[2:].zfill(8)
        else:
            upper_val = str(upper).zfill(8)
        
        # The axi_user_id is expected to be a string (e.g., "CALIPTRA_AXI_USER_ID0").
        axi_id_val = axi_user_id if isinstance(axi_user_id, str) else f"4'd{axi_user_id}"
        
        entry_str = "  '{ lower_addr: 32'h%s, upper_addr: 32'h%s, axi_user_id: %s }" % (
            lower_val, upper_val, axi_id_val)
        if idx < num_entries - 1:
            entry_str += ","
        entries_sv.append(entry_str)
    
    table_footer = "\n};\n"
    
    # Append endif for the include guard.
    endif_footer = "\n`endif // FC_ACCESS_CONTROL_TABLE_SV\n"
    
    # Combine all parts.
    return license_header + table_header + "\n".join(entries_sv) + table_footer + endif_footer

def main():
    args = parse_args()
    entries = load_entries(args.hjson)
    sv_code = generate_sv(entries)
    try:
        with open(args.sv_out, "w") as f:
            f.write(sv_code)
        print("SystemVerilog access control table generated in:", args.sv_out)
    except Exception as e:
        sys.exit(f"Error writing output file {args.sv_out}: {e}")

if __name__ == "__main__":
    main()
