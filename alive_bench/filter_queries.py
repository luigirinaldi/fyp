# Filter out the queries using the same criteria as in the "Towards Satisfiability Modulo Parametric Bit-vectors -- Artifact"

import json
import os
import sys
import shutil
import re 
from parse_smt import parse_smt
from io import StringIO


def sat_mod_parametric(name_filter, output_dir):
    input_dir = "bv_to_bool_bench"

    shutil.rmtree(output_dir, ignore_errors=True)
    # Ensure output directory exists
    os.makedirs(output_dir, exist_ok=True)

    # Regex pattern for matching filenames
    pattern = re.compile(r"(.*)_values_\d+\.smt2$")

    # Iterate over files in input directory
    count = 0
    
    ret_vals = {}
    
    for filename in os.listdir(input_dir):
        if (match := pattern.match(filename)) and match.group(1) in name_filter:
            with open(input_dir + '/' + filename, 'r') as q_candidate:
                if "(_ BitVec 4)" in (file_contents:="".join(q_candidate.readlines())):
                    ret_vals[match.group(1)] = (file_contents, filename)
                    print(filename)
                    src = os.path.join(input_dir, filename)
                    dst = os.path.join(output_dir, filename)
                    shutil.copy2(src, dst)
                    count += 1

    print(f"{count} Matching files copied to '{output_dir}'.")
    return ret_vals

def main():
    if len(sys.argv) != 2:
        print("Usage: python filter_values_4.py list.txt")
        sys.exit(1)

    list_file = sys.argv[1]
    # Validate list file
    if not os.path.isfile(list_file):
        print(f"Error: List file '{list_file}' not found.")
        sys.exit(1)

    # Load names from list
    with open(list_file, "r") as f:
        allowed_names = set(line.strip() for line in f if line.strip())
    
    output_dir = "filtered_values"

    filtered_files = sat_mod_parametric(allowed_names, output_dir)
    
    bw_dir = "valid_queries"

    shutil.rmtree(bw_dir, ignore_errors=True)
    # Ensure output directory exists
    os.makedirs(bw_dir, exist_ok=True)
    
    out_files = {
        '00': [],
        '01': [],
        '10': [],
        '11': []
    }
    
    cond_count = 0
    count = 0
    for filename_clean, (filestr, filename) in filtered_files.items():
        # print(filename, filestr)
        try:
            (lhs, rhs, preconds), is_bitwise, is_arith = parse_smt(StringIO(filestr))
            bw_lang_expr = {
                "name": filename_clean.strip().replace(':', '_').replace('-', '_'),
                "lhs": lhs,
                "rhs": rhs,
                "preconditions": preconds
            }
            
            out_files[f'{is_bitwise:d}{is_arith:d}'].append(bw_lang_expr)
            
            print(filename_clean)
            src = os.path.join(output_dir, filename)
            dst = os.path.join(bw_dir, filename)
            shutil.copy2(src, dst)
            if preconds != []:
                cond_count += 1
            count += 1
        except AssertionError as e:
            print(f"Skipped {filename} because {e}")
    
    print(f"{count} Total queries, {count - cond_count} are unconditional, {cond_count} are conditional")
    print(f"{len(out_files['10'])} bitwise expressions, {len(out_files['01'])} arithmetic expressions, {len(out_files['11'])} mixed-expressions and {len(out_files['00'])} expression which are neither")
    
    
    with open("../test_data/alive_arith.json", "w") as f:
        json.dump(out_files["01"] + out_files["00"], f, indent=2)
    with open("../test_data/alive_bitwise.json", "w") as f:
        json.dump(out_files["10"], f, indent=2)
    with open("../test_data/alive_mixed.json", "w") as f:
        json.dump(out_files["11"], f, indent=2)
if __name__ == "__main__":
    main()