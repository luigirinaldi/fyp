import os
import re
import json
import argparse
from collections import defaultdict

def parse_arguments():
    parser = argparse.ArgumentParser(description="Parse SMT2 log and err files with prefixes.")
    parser.add_argument("input_folder", help="Path to the folder containing the .smt2, .log, and .err files")
    parser.add_argument("output_file", help="Path to output JSON file")
    return parser.parse_args()

def main():
    args = parse_arguments()
    folder_path = args.input_folder
    output_json = args.output_file

    # Valid prefixes to search for
    valid_prefixes = ["combined", "full", "qf", "partial"]

    pattern = re.compile(rf"^({'|'.join(valid_prefixes)})-\1_(.*)_values_\d+\.smt2.log")
    time_re = re.compile(r"\[runlim\] real:\s+([\d.]+) seconds")

    results = defaultdict(dict)

    for filename in os.listdir(folder_path):
        match = pattern.match(filename)
        if match:
            prefix, some_name = match.group(1), match.group(2)

            log_path = os.path.join(folder_path, filename)
            err_path = os.path.join(folder_path, filename.replace('.log', '') + ".err")
            status = None
            time_taken = None

            assert os.path.exists(log_path)
            with open(log_path, 'r') as f:
                log_content = f.read()
                if "unsat" in log_content:
                    status = "unsat"
                elif "sat" in log_content:
                    status = "sat"
                elif "unknown" in log_content:
                    status = "unknown"


            assert os.path.exists(err_path)
            with open(err_path, 'r') as f:
                for line in f:
                    time_match = time_re.search(line)
                    if time_match:
                        time_taken = float(time_match.group(1))
                        break

            results[some_name][prefix] = {
                "status": status or 'timeout',
                "time": time_taken
            }

    # print(f"{len(results.keys())} smt queries found")
    assert len(results.keys()) == 180

    with open(output_json, "w") as out_file:
        json.dump(results, out_file, indent=2)

    print(f"Results written to {output_json}")

if __name__ == "__main__":
    main()
