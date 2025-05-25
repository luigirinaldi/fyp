import os
import sys
import shutil

def main():
    if len(sys.argv) != 2:
        print("Usage: python filter_values_4.py list.txt")
        sys.exit(1)

    list_file = sys.argv[1]
    input_dir = "bv_to_bool_bench"
    output_dir = "filtered_values"

    # Validate list file
    if not os.path.isfile(list_file):
        print(f"Error: List file '{list_file}' not found.")
        sys.exit(1)

    # Load names from list
    with open(list_file, "r") as f:
        allowed_names = set(line.strip() for line in f if line.strip())

    # Ensure output directory exists
    os.makedirs(output_dir, exist_ok=True)

    # Regex pattern for matching filenames
    # pattern = re.compile(r"^([^:]+):\d+_values_4\.smt2$")

    # Iterate over files in input directory
    count = 0
    for filename in os.listdir(input_dir):
        if filename.endswith("_values_4.smt2"):
            # print(filename)
            if filename.replace("_values_4.smt2", "") in allowed_names:
                print(filename)
                src = os.path.join(input_dir, filename)
                dst = os.path.join(output_dir, filename)
                shutil.copy2(src, dst)
                count += 1

    print(f"{count} Matching files copied to '{output_dir}'.")

if __name__ == "__main__":
    main()