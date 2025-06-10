#!/bin/sh

# --- Input Arguments ---
# Usage: ./script.sh (BIN_PATH)

SRC_DIR="./test_data"
DEST_DIR="./gen_graphs/data"

BIN_PATH="./target/release/hello-world"

cargo build --release

# --- Get Timings ---

find "$SRC_DIR" -type f -name "*.json" | while read -r file; do
  base_name=$(basename "$file" .json)

  OUT_DIR="$DEST_DIR/${base_name}"

  echo "Gathering data for $base_name"

  "$BIN_PATH" "$file" --runner-stats "$OUT_DIR/egraph_stats.json" > /dev/null
done

cargo build --release --features get-heap-info

# --- Get Meminfo ---

# find "$SRC_DIR" -type f -name "*.json" | while read -r file; do
#   base_name=$(basename "$file" .json)

#   OUT_DIR="$DEST_DIR/${base_name}"

#   echo "Gathering mem data for $base_name"

#   "$BIN_PATH" "$file" --runner-stats "$OUT_DIR/egraph_stats_mem.json" > /dev/null
# done
