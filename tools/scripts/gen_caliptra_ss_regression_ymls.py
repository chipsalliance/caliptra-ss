##********************************************************************************
## SPDX-License-Identifier: Apache-2.0
## Copyright 2020 Western Digital Corporation or its affiliates.
##
## Licensed under the Apache License, Version 2.0 (the "License");
## you may not use this file except in compliance with the License.
## You may obtain a copy of the License at
##
## http:##www.apache.org/licenses/LICENSE-2.0
##
## Unless required by applicable law or agreed to in writing, software
## distributed under the License is distributed on an "AS IS" BASIS,
## WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
## See the License for the specific language governing permissions and
## limitations under the License.
##********************************************************************************

import csv
import os
import logging
import glob
import pprint
from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import DoubleQuotedScalarString
from ruamel.yaml.comments import CommentedMap, CommentedSeq
import re

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Add file handler for DEBUG level
file_handler = logging.FileHandler('debug.log')
file_handler.setLevel(logging.DEBUG)
file_handler.setFormatter(logging.Formatter('%(asctime)s - %(levelname)s - %(message)s'))
logger.addHandler(file_handler)

def generate_output_filename(csv_file_path, criteria):
    # Check if this is an L0 Promote yaml
    if criteria.get("L0") == "L0" and criteria.get("PromotePipeline") == "Promote":
        # Use only L0, PromotePipeline, and DUT for L0 Promote yaml
        parts = []
        for key in ["L0", "PromotePipeline", "DUT"]:
            if criteria.get(key):
                parts.append(criteria[key])
    else:
        # Use all criteria for non-L0 Promote yaml
        parts = []
        for key in ["L0", "L1", "Nightly|Weekly", "PromotePipeline", "Directed|Random", "DUT"]:
            if criteria.get(key):
                parts.append(criteria[key])
    
    parent_directory = os.path.dirname(os.path.dirname(csv_file_path))
    filename = "_".join(parts) + "_regression.yml"
    return os.path.join(parent_directory, filename)

def csv_to_yaml(csv_file_path, yml_file_path, criteria, generations):
    # Required headers
    required_headers = ["TestName", "Directed|Random", "Nightly|Weekly", "L0", "L1", "DUT", "PromotePipeline", "OtherTags", "Weight"]

    # Read the CSV file and filter the data
    filtered_data = []
    with open(csv_file_path, mode='r', encoding='utf-8') as csv_file:
        csv_reader = csv.DictReader(csv_file)
        headers = [header.strip() for header in csv_reader.fieldnames]

        # Debug: Log headers
        logger.debug(f"CSV Headers: {headers}")

        # Check for required headers
        for header in required_headers:
            if header not in headers:
                raise KeyError(f"Required header '{header}' not found in the CSV file.")

        # Debug: Log a sample row
        for row in csv_reader:
            logger.debug(f"Sample row: {row}")
            break  # Just log the first row for debugging

    # Re-read the CSV file and filter the data
    with open(csv_file_path, mode='r', encoding='utf-8') as csv_file:
        csv_reader = csv.DictReader(csv_file)
        logger.debug(f"Looking for rows that match criteria: {criteria}")
        
        for row in csv_reader:
            # Strip spaces from keys and values in each row
            row = {key.strip(): value.strip() for key, value in row.items()}

            # Special handling for L0 Promote
            # L0 Promote tests
            if criteria.get("L0") == "L0" and criteria.get("PromotePipeline") == "Promote":
                dut_match = (row["DUT"] == criteria["DUT"])
                promote_match = (row["PromotePipeline"] == "Promote")
                l0_match = (row["L0"] == "L0" or row["L0"] == "None" or row["L0"] == "")
                all_match = dut_match and promote_match and l0_match
            elif criteria.get("L1") == "L1":
                dir_rand_match = (row["Directed|Random"] == criteria["Directed|Random"] or row["Directed|Random"] == "None")
                nw_match = (row["Nightly|Weekly"] == criteria["Nightly|Weekly"] or row["Nightly|Weekly"] == "None")
                l1_match = (row["L1"] == "L1")
                not_l0_only = not (row["L0"] == "L0" and row["L1"] != "L1")
                dut_match = (row["DUT"] == criteria["DUT"])
                promote_match = (criteria["PromotePipeline"] == row["PromotePipeline"] or criteria["PromotePipeline"] is None)
                all_match = dir_rand_match and nw_match and l1_match and not_l0_only and dut_match and promote_match
            if all_match:
                logger.debug(f"✅ MATCHED: {row['TestName']}")
                filtered_data.append(row)
            else:
                logger.debug(f"❌ NOT MATCHED: {row['TestName']}")

    # Debug: Log filtered data
    logger.debug(f"Filtered data size: {len(filtered_data)}")
    logger.debug("Filtered data details:")
    for item in filtered_data:
        logger.debug(f"  - {item['TestName']}")

    # Create the new YAML structure for L0 Promote tests
    # Use ruamel.yaml for better control over YAML formatting
    yaml = YAML()
    yaml.default_flow_style = False
    yaml.indent(sequence=4, offset=2)

    # Check if this is
    # * L0 Promote regression
    # * Nightly Directed regression
    if (criteria.get("L0") == "L0" and criteria.get("PromotePipeline") == "Promote") or (criteria.get("L1") == "L1" and criteria.get("Directed|Random") == "Directed"):
        # Create the new L0 Promote structure
        document = CommentedMap()
        document["document"] = CommentedMap([('schema', 1.0)])
        
        contents = CommentedSeq()
        tests_map = CommentedMap()
        
        # Create tags list with flow style
        if (criteria.get("L0") == "L0"):
            tags = CommentedSeq(["L0"])  # L0 is always required for L0 Promote
        else:
            tags = CommentedSeq(["L1"])  # L1 is always required for L1 Directed
        
        # Add tags from OtherTags
        if criteria.get("OtherTags"):
            existing_tags = set(tags)
            other_tags = criteria["OtherTags"].split(',')
            for tag in other_tags:
                tag = tag.strip()
                if tag and tag not in existing_tags:  # Skip empty tags and duplicates
                    tags.append(tag)
                    existing_tags.add(tag)
        
        # Set flow style for compact array notation
        tags.fa.set_flow_style()
        
        tests_map["tags"] = tags
        
        # Create paths list
        paths = CommentedSeq()
        for row in filtered_data:
            # Format the path properly
            test_path = row["TestName"]
            
            # If the test path is in the format "ip_name/path/to/test.yml", 
            # convert it to "../test_suites/path/to/test.yml"
            if '/' in test_path:
                # Skip the IP name part and use the rest of the path
                test_parts = test_path.split('/', 3)
                test_path = f"../{test_parts[3]}.yml"
            else:
                test_path = f"../test_suites/{test_path}"
                if not (test_path.endswith('.yml') or test_path.endswith('.yaml')):
                    test_path += '.yml'
                
            paths.append(test_path)
        
        tests_map["paths"] = paths
        
        # Add tests map to contents
        tests_entry = CommentedMap()
        tests_entry["tests"] = tests_map
        contents.append(tests_entry)
        
        # Write the document to the file 
        if criteria.get("Directed|Random") == "Directed":
            modded_yml_path = re.sub(r"_Directed_", "_Directed_Strict_", yml_file_path)
        else:
            modded_yml_path = yml_file_path
        with open(modded_yml_path, 'w', encoding='utf-8') as yml_file:
            # Write document part
            yml_file.write("document:\n")
            yml_file.write("  schema: 1.0\n")
            yml_file.write("\n")  # Extra line break
            
            # Write contents part
            yml_file.write("contents:\n")
            # Write tests-based format manually for L0 Promote
            yml_file.write("  - tests:\n")
            
            # Write tags with flow style
            yml_file.write("      tags: ")
            yml_file.write(str(tags).replace("'", "\""))
            yml_file.write("\n")
            
            # Write paths
            yml_file.write("      paths:\n")
            for path in paths:
                yml_file.write(f"        - {path}\n")
            
    if not (criteria.get("L0") == "L0" and criteria.get("PromotePipeline") == "Promote"):
        # For non-L0 Promote, use the generator format
        # Adjust generations based on criteria
        template_count = len(filtered_data)
        if template_count > 0:
            adjusted_generations = max(generations, template_count * 10)
            logger.info(f"Setting generations to {adjusted_generations} (10x template count)")
            generations = adjusted_generations
        else:
            logger.warning(f"No templates matched for criteria: {criteria}")

        # Prepare the YAML structure using CommentedMap and CommentedSeq for better control
        tags = CommentedSeq([DoubleQuotedScalarString(criteria[key]) for key in ["L0", "L1", "DUT", "Directed|Random", "Nightly|Weekly"] if criteria[key] is not None])
        
        # Add OtherTags if it's not None
        if criteria.get("OtherTags"):
            tags.append(DoubleQuotedScalarString(criteria["OtherTags"]))
        tags.fa.set_flow_style()

        generator_data = CommentedMap()
        generator_data['generator'] = CommentedMap()
        generator_data['generator']['tags'] = tags
        generator_data['generator']['path'] = DoubleQuotedScalarString("")
        generator_data['generator']['weight'] = 100
        generator_data['generator']['generations'] = generations
        
        # Use different formats based on PromotePipeline
        if criteria.get("PromotePipeline") == "Promote":
            generator_data['generator']['formats'] = CommentedMap([
                ('generate', DoubleQuotedScalarString("reseed {template}.yml -seed 1")),
                ('path', DoubleQuotedScalarString("{template_basename}__1.yml"))
            ])
        else:
            generator_data['generator']['formats'] = CommentedMap([
                ('generate', DoubleQuotedScalarString("reseed {template}.yml -seed {seed}")),
                ('path', DoubleQuotedScalarString("{template_basename}__{seed}.yml"))
            ])
            
        templates = CommentedMap()
        for row in filtered_data:
            template_path = row["TestName"]
            templates[template_path] = CommentedMap([('weight', int(row["Weight"]))])
            templates[template_path].fa.set_flow_style()

        generator_data['generator']['templates'] = templates

        # Add timeout if specified
        if "timeout" in criteria:
            generator_data["generator"]["config"] = {
                "params": {
                    "timeout": criteria["timeout"]
                }
            }

        # Wrap generator_data in a list for the contents section
        contents = CommentedSeq([generator_data])
        
        # Create the final document structure
        document = CommentedMap()
        document["document"] = CommentedMap([('schema', 1.0)])  # Add schema version
        document["contents"] = contents

        # Write the document to the file 
        with open(yml_file_path, mode='w', encoding='utf-8') as yml_file:
            # Write document part
            yml_file.write("document:\n")
            yml_file.write("  schema: 1.0\n")
            #yml_file.write("\n")  # Extra line break
            
            # Write contents part
            yml_file.write("contents:\n")
            # Write generator-based format manually
            yml_file.write("  - generator:\n")
            
            # Write tags
            yml_file.write("      tags: ")
            yml_file.write(str(generator_data['generator']['tags']).replace("'", "\""))
            yml_file.write("\n")
            
            # Write path
            yml_file.write(f"      path: \"{generator_data['generator']['path']}\"\n")
            
            # Write weight
            yml_file.write(f"      weight: {generator_data['generator']['weight']}\n")
            
            # Write generations
            yml_file.write(f"      generations: {generator_data['generator']['generations']}\n")
            
            # Write formats
            yml_file.write("      formats:\n")
            for key, value in generator_data['generator']['formats'].items():
                yml_file.write(f"        {key}: \"{value}\"\n")
            
            # Write templates
            yml_file.write("      templates:\n")
            for template_path, template_config in generator_data['generator']['templates'].items():
                yml_file.write(f"        {template_path}: {{ weight: {template_config['weight']} }}\n")
            
            # Write config if present
            if 'config' in generator_data['generator']:
                yml_file.write("      config:\n")
                yml_file.write("        params:\n")
                yml_file.write(f"          timeout: {generator_data['generator']['config']['params']['timeout']}\n")

        # Log templates section for debugging
        logger.debug(f"Templates in YAML: {pprint.pformat(templates)}")

        # Post-process the generated YAML file to fix lines with question marks and extra colons
        with open(yml_file_path, mode='r', encoding='utf-8') as yml_file:
            lines = yml_file.readlines()

        with open(yml_file_path, mode='w', encoding='utf-8') as yml_file:
            previous_line = None
            for line in lines:
                logger.debug(f"Current line: {line}")
                if line.strip().startswith('contents'):
                    yml_file.write('\n')
                    yml_file.write(line)
                elif re.search(r'^\s*\?\s*', line):
                    logger.debug(f"Question mark line: {line}")
                    indent = re.match(r'^\s*', line).group(0)
                    line = re.sub(r'^\s*\?\s*', '', line)
                    previous_line = f'{indent}{line.rstrip()}'
                elif re.search(r'^\s*\:\s*', line):
                    logger.debug(f"Colon line: {line}")
                    logger.debug(f"Previous line: {previous_line}")
                    indent = re.match(r'^\s*', line).group(0)
                    line = re.sub(r'^\s*\:\s*', '', line)
                    current_line = f'{indent}{line}'
                    yml_file.write(f'{previous_line}: {current_line}')
                    previous_line = None
                elif re.search(r'\s+\{$', line):
                    indent = re.match(r'^\s*', line).group(0)
                    line = re.sub(r'^\s*', '', line)
                    previous_line = f'{indent}{line.rstrip()}'
                    logger.debug(f"Modified to {previous_line}")
                elif re.search(r'^\s*weight', line) and previous_line is not None:
                    line = re.sub(r'^\s*', '', line)
                    yml_file.write(f'{previous_line} {line.rstrip()}\n')
                    previous_line = None
                else:
                    if previous_line:
                        yml_file.write(f'{previous_line}\n')
                        previous_line = None
                    yml_file.write(line)

def scan_test_suites(caliptra_ss):
    ############################################################################
    # Scan through all src/<ip>/test_suites/ directories and print a list of all test names,
    # excluding 'includes' and 'libs' directories.
    #
    # Args:
    #    caliptra_ss (str): The root directory of the Caliptra project
    #
    # Returns:
    #    list: A list of all test names found
    #############################################################################

    logger.info("Scanning for test suites...")
    
    # Create the pattern to match src/<ip>/test_suites/ directories
    search_pattern = os.path.join(caliptra_ss, "src", "*", "test_suites")
    
    # Find all test_suites directories
    test_suite_dirs = glob.glob(search_pattern)
    logger.debug(f"Found {len(test_suite_dirs)} test_suites directories: {test_suite_dirs}")
    
    all_tests = []
    
    # Scan each test_suites directory
    for test_dir in test_suite_dirs:
        ip_name = os.path.basename(os.path.dirname(test_dir))
        logger.info(f"Scanning tests for IP: {ip_name}")
        
        # Walk through each directory
        for root, dirs, files in os.walk(test_dir):
            # Skip 'includes' and 'libs' directories
            if 'includes' in dirs:
                dirs.remove('includes')
            if 'libs' in dirs:
                dirs.remove('libs')
            
            # Look for YAML test files
            for file in files:
                if file.endswith('.yml') or file.endswith('.yaml'):
                    # Get relative path from test_dir
                    rel_path = os.path.relpath(os.path.join(root, file), test_dir)
                    # Format as a test name
                    test_name = f"{ip_name}/{rel_path}"
                    all_tests.append(test_name)
    
    # Sort the tests for better readability
    all_tests.sort()
    
    # Print the results
    logger.info(f"Found {len(all_tests)} tests:")
    for test in all_tests:
        logger.info(f"  - {test}")
    
    return all_tests



if __name__ == "__main__":
    caliptra_ss = os.getenv('CALIPTRA_SS_ROOT')

    if not caliptra_ss:
        logger.error("CALIPTRA_SS_ROOT environment variable is not set. Please set it before running this script.")
        exit(1)
    
    # Scan for all test suites first
    #all_tests = scan_test_suites(caliptra_ss)

    csv_file_path = os.path.join(caliptra_ss, 'src/integration/stimulus/testsuites/caliptra_ss_master_test_list.csv')

    # Debug: Display CSV contents
    logger.info("CSV file contents:")
    try:
        with open(csv_file_path, mode='r', encoding='utf-8') as csv_file:
            for i, line in enumerate(csv_file):
                if i < 10:  # Show first 10 lines
                    logger.info(f"Line {i}: {line.strip()}")
                else:
                    break
    except Exception as e:
        logger.error(f"Error reading CSV file: {e}")

    combinations = [
        {"Directed|Random": None, "Nightly|Weekly": None, "L0": "L0", "L1": None, "DUT": "caliptra_ss_top_tb", "PromotePipeline": "Promote", "OtherTags": "Lop_regression,top_regression"},  
        {"Directed|Random": "Directed", "Nightly|Weekly": "Nightly", "L0": None, "L1": "L1", "DUT": "caliptra_ss_top_tb", "PromotePipeline": None},
        {"Directed|Random": "Random", "Nightly|Weekly": "Nightly", "L0": None, "L1": "L1", "DUT": "caliptra_ss_top_tb", "PromotePipeline": None}
    ]

    for criteria in combinations:
        output_filename = generate_output_filename(csv_file_path, criteria)
        logger.info(f"Creating YAML file '{output_filename}' with criteria: {criteria}")
        csv_to_yaml(csv_file_path, output_filename, criteria, 1) # Default to 1, will be adjusted based on template count
        logger.info(f"YAML file '{output_filename}' successfully created.")
