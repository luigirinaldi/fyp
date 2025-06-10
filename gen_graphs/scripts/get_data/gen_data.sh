#!/bin/sh

# --- Input Arguments ---
# Usage: ./script.sh [TIMEOUT] [ISABELLE_PATH]

SLEDGEHAMMER_TIMEOUT=${1:-300}
ISABELLE_PATH=${2:-isabelle}

# Try running the version command
if ! "$ISABELLE_PATH" version; then
    echo "Error: Program at $ISABELLE_PATH failed to run or return version"
    exit 1
fi

SRC_DIR="./test_data"
DEST_DIR="./gen_graphs/tmp"
BIN_PATH="./target/release/hello-world"

# Build the tool
cargo build --release

# Empty and recreate destination directory
rm -rf "$DEST_DIR"
mkdir -p "$DEST_DIR"

# --- Functions ---
run_mirabelle() {
  DIR="$1"
  BASE_NAME="$2"
  MODE="$3"  # either "lemma" or "no_lemma"

  ROOT_FILE="$DIR/ROOT"
  > "$ROOT_FILE"

  cp ./proofs/rewrite_lemmas.thy "$DIR"
  cp ./proofs/rewrite_defs.thy "$DIR"

  echo "session LemmaSledge = HOL +" >> "$ROOT_FILE"
  echo "options [quick_and_dirty]" >> "$ROOT_FILE"
  echo "theories" >> "$ROOT_FILE"

  DATA_OUT_DIR="./gen_graphs/data/$BASE_NAME/$MODE"
  mkdir -p "$DATA_OUT_DIR"

  sys_data="$DATA_OUT_DIR/system.json"
  echo "[" >> "$sys_data"

  find "$DIR" -type f -name "*.thy" | while read -r file; do
    base_name=$(basename "$file")
    name_only="${base_name%.thy}"

    # Skip helper theory files
    if [ "$name_only" = "rewrite_lemmas" ] || [ "$name_only" = "rewrite_defs" ]; then
      continue
    fi

    echo "  $name_only" >> "$ROOT_FILE"
    echo "Mirabelle running for $name_only ($MODE)"

    stdbuf -oL /usr/bin/time --output="$sys_data" -a --format="{\"name\":\"$name_only\", \"cpu\":\"%P\", \"mem\":%M}," \
      "$ISABELLE_PATH" mirabelle -d "$DIR" -O "$DIR/mirabelle_out" \
      -A "try0" -A "sledgehammer[timeout=$SLEDGEHAMMER_TIMEOUT]" \
      -T "$name_only" LemmaSledge | sed 's/^/[mirabelle] /'
  done

  echo "]" >> "$sys_data"

  cp "$DIR/mirabelle_out/mirabelle.log" "$DATA_OUT_DIR/mirabelle.log"
  python ./gen_graphs/parse_mirabelle.py "$DIR/mirabelle_out/mirabelle.log" "$DATA_OUT_DIR/parsed.json"
}

# --- Main Processing Loop ---

find "$SRC_DIR" -type f -name "*.json" | while read -r file; do
  base_name=$(basename "$file" .json)

  LEMMA_DIR="$DEST_DIR/${base_name}/lemma"
  NO_LEMMA_DIR="$DEST_DIR/${base_name}/no_lemma"

  mkdir -p "$LEMMA_DIR"
  mkdir -p "$NO_LEMMA_DIR"

  echo "Generating theorems for $base_name"

  # Execute tool: no lemma
  "$BIN_PATH" "$file" --skip-equiv --theorem-path "$NO_LEMMA_DIR" --def-only > /dev/null

  # Execute tool: with lemma
  "$BIN_PATH" "$file" --skip-equiv --theorem-path "$LEMMA_DIR" > /dev/null

  # Run Mirabelle
  run_mirabelle "$NO_LEMMA_DIR" "$base_name" "no_lemma"
  run_mirabelle "$LEMMA_DIR" "$base_name" "lemma"
done
