# Filter out the queries using the same criteria as in the "Towards Satisfiability Modulo Parametric Bit-vectors -- Artifact"

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
                    ret_vals[filename] = file_contents
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
    
    non_cond_dir = "non_cond_query"

    shutil.rmtree(non_cond_dir, ignore_errors=True)
    # Ensure output directory exists
    os.makedirs(non_cond_dir, exist_ok=True)
    
    count = 0
    for filename, filestr in filtered_files.items():
        # print(filename, filestr)
        try:
            parse_smt(StringIO(filestr))
            src = os.path.join(output_dir, filename)
            dst = os.path.join(non_cond_dir, filename)
            shutil.copy2(src, dst)
            count += 1
        except AssertionError:
            print(f"Skipped {filename}")
    
    print(f"{count} Queries are unconditional")


if __name__ == "__main__":
    main()