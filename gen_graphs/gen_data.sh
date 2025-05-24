#!/bin/sh

SLEDGEHAMMER_TIMEOUT=300

ISABELLE_PATH="isabelle"

# Try running the version command
if ! "$ISABELLE_PATH" version; then
    echo "Error: Program at $ISABELLE_PATH failed to run or return version";
    return;
fi


SRC_DIR="./test_data"
DEST_DIR="./gen_graphs/tmp"
LEMMA_DIR="$DEST_DIR/lemma"
NO_LEMMA_DIR="$DEST_DIR/no_lemma"

echo "$LEMMA_DIR"

BIN_PATH="./target/release/hello-world"

# Build the tool
cargo build --release

# Empty destination directory and recreate it
rm -rf "$DEST_DIR"
mkdir -p "$DEST_DIR"
mkdir "$LEMMA_DIR"
mkdir "$NO_LEMMA_DIR"

find "$SRC_DIR" -type f -name "*.json" | while read -r file; do
  base_name=$(basename "$file")
  echo "Generating theorems for $base_name"
  # Execute the tool (no lemma)
  "$BIN_PATH" "$file" --skip-equiv --theorem-path "$NO_LEMMA_DIR" --def-only > /dev/null
  # Execute the tool (with lemma)
  "$BIN_PATH" "$file" --skip-equiv --theorem-path "$LEMMA_DIR" > /dev/null
done

# --- Functions ---
run_mirabelle() {
  DIR="$1"
  ROOT_FILE="$DIR/ROOT"

  # Clear the ROOT file if it exists
  > "$ROOT_FILE"

  cp ./proofs/rewrite_lemmas.thy "$DIR"
  cp ./proofs/rewrite_defs.thy "$DIR"

  echo "session LemmaSledge = HOL +" >> "$ROOT_FILE"
  echo "options [quick_and_dirty]" >> "$ROOT_FILE"
  echo "theories" >> "$ROOT_FILE"

  DATA_OUT_PRE="./gen_graphs/data/$(basename "$DIR")"
  sys_data="$DATA_OUT_PRE"_system.json
  echo "[" >> "$sys_data"
  count=0
  find "$DIR" -type f -name "*.thy" | while read -r file; do
    # if [ "$count" -ge 3 ]; then
    #   break
    # fi
    base_name=$(basename "$file")
    name_only="${base_name%.thy}"

    # Skip specific theory files
    if [ "$name_only" = "rewrite_lemmas" ] || [ "$name_only" = "rewrite_defs" ]; then
      continue
    fi

    echo "  $name_only" >> "$ROOT_FILE"
    echo "Mirabelle running for $name_only"

    stdbuf -oL /usr/bin/time --output="$sys_data" -a --format="{\"name\":\""$name_only"\", \"cpu\":\"%P\", \"mem\":%M}," \
                "$ISABELLE_PATH" mirabelle -d "$DIR" -O "$DIR/mirabelle_out" \
                -A "try0" -A "sledgehammer[timeout=$SLEDGEHAMMER_TIMEOUT]" \
                -T "$name_only" LemmaSledge | sed 's/^/[mirabelle] /'
    count=$((count + 1))
  done
  echo "]" >> "$sys_data"
  cp "$DIR/mirabelle_out/mirabelle.log" "$DATA_OUT_PRE""_mirabelle.log"
  python ./gen_graphs/parse_mirabelle.py "$DIR/mirabelle_out/mirabelle.log" "$DATA_OUT_PRE"".json"
}

# --- Run for both directories ---

mkdir -p "./gen_graphs/data"

run_mirabelle "$NO_LEMMA_DIR"
run_mirabelle "$LEMMA_DIR"

