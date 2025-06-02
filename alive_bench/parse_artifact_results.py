import os
import re
import json
import argparse

def parse_arguments():
    parser = argparse.ArgumentParser(description="Parse SMT2 log and err files.")
    parser.add_argument("input_folder", help="Path to the folder containing the .smt2, .log, and .err files")
    parser.add_argument("output_file", help="Path to output JSON file")
    return parser.parse_args()

def main():
    args = parse_arguments()
    folder_path = args.input_folder
    output_json = args.output_file

    filename_re = re.compile(r".*_([a-zA-Z0-9]+):(\d+)_values_(\d+)\.smt2")
    time_re = re.compile(r"\[runlim\] real:\s+([\d.]+) seconds")

    results = {}

    for filename in os.listdir(folder_path):
        match = filename_re.match(filename)
        if match:
            some_name = match.group(1)
            base_name = filename.rsplit('.smt2', 1)[0]

            log_path = os.path.join(folder_path, base_name + ".log")
            err_path = os.path.join(folder_path, base_name + ".err")

            status = "unknown"
            time_taken = None

            # Read status from log file
            if os.path.exists(log_path):
                with open(log_path, 'r') as f:
                    log_content = f.read()
                    if "unsat" in log_content:
                        status = "unsat"
                    elif "sat" in log_content:
                        status = "sat"
                    elif "unknown" in log_content:
                        status = "unknown"

            # Read time from err file
            if os.path.exists(err_path):
                with open(err_path, 'r') as f:
                    for line in f:
                        time_match = time_re.search(line)
                        if time_match:
                            time_taken = float(time_match.group(1))
                            break

            results[some_name] = {
                "status": status,
                "time": time_taken
            }

    with open(output_json, "w") as out_file:
        json.dump(results, out_file, indent=2)

    print(f"Results written to {output_json}")

if __name__ == "__main__":
    main()
