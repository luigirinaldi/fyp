#!/bin/sh

# --- Input Arguments ---
# Usage: ./script.sh (BIN_PATH)

BIN_PATH=$1

SRC_DIR="./test_data"
DEST_DIR="./gen_graphs/data"

# --- Main Processing Loop ---

find "$SRC_DIR" -type f -name "*.json" | while read -r file; do
  base_name=$(basename "$file" .json)

  OUT_DIR="$DEST_DIR/${base_name}"

  echo "Gathering data for $base_name"

  # Execute tool: no lemma
  "$BIN_PATH" "$file" --runner-stats "$OUT_DIR/egraph_stats.json" > /dev/null
done
