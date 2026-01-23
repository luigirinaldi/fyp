"""
This is a file to automatically generate the mappings from lemma name to .thy file.

Run this from inside of this directory to create the corresponding rust file.
"""

import os
import re
from pathlib import Path

# ---------------- CONFIG ----------------

SEARCH_DIR = "../proofs"
FILENAME_SUBSTRING = "_lemmas.thy"

OUTPUT_RUST_FILE = "../src/generated_matcher.rs"
RUST_FUNCTION_NAME = "rule_to_file"

# ----------------------------------------


def collect_matches(directory):
    compiled = re.compile(r"lemma ([^:]+):.*")
    results = {}

    for root, _, files in os.walk(directory):
        for filename in files:
            if not filename.endswith(FILENAME_SUBSTRING):
                continue

            file_path = Path(root) / filename

            try:
                text = file_path.read_text(encoding="utf-8", errors="ignore")
            except Exception as e:
                print(f"Skipping {file_path}: {e}")
                continue

            matches = compiled.findall(text)

            for match in matches:
                results[match] = filename.replace(".thy", "")

    return results


def generate_rust(match_map, output_file, function_name):
    with open(output_file, "w", encoding="utf-8") as f:
        f.write("/*\nAUTO-GENERATED FILE — DO NOT EDIT\n*/\n")
        f.write(f"pub fn {function_name}(input: &str) -> Option<&'static str> {{\n")
        f.write("    match input {\n")

        for key, value in sorted(match_map.items()):
            f.write(f'        "{key}" => Some("{value}"),\n')

        f.write("        _ => None,\n")
        f.write("    }\n")
        f.write("}\n")

    print(f"Rust file generated: {output_file}")


def main():
    print("Scanning directory...")
    matches = collect_matches(
        SEARCH_DIR,
    )

    print(f"Found {len(matches)} unique pattern matches")

    generate_rust(matches, OUTPUT_RUST_FILE, RUST_FUNCTION_NAME)


if __name__ == "__main__":
    main()
