#!/bin/sh

SLEDGEHAMMER_TIMEOUT=300

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
  echo "Running for $base_name"
  # Execute the tool (no lemma)
  "$BIN_PATH" "$file" --skip-equiv --theorem-path "$NO_LEMMA_DIR" --def-only
  # Execute the tool (with lemma)
  "$BIN_PATH" "$file" --skip-equiv --theorem-path "$LEMMA_DIR"
done


# Clear the ROOT file if it exists
ROOT_FILE="$LEMMA_DIR/ROOT"
> "$ROOT_FILE"

cp ./proofs/rewrite_lemmas.thy "$LEMMA_DIR"
cp ./proofs/rewrite_defs.thy "$LEMMA_DIR"

echo "session LemmaSledge = HOL +
options [quick_and_dirty]
theories
  rewrite_lemmas" >> "$ROOT_FILE"

find "$LEMMA_DIR" -type f -name "*.thy" | while read -r file; do
  base_name=$(basename "$file")
  name_only="${base_name%.thy}"

  # Append name without extension to the ROOT file
  echo "  $name_only" >> "$ROOT_FILE"

  # Run Mirabelle on the newly appended theory
  isabelle mirabelle -d "$LEMMA_DIR" -O "$LEMMA_DIR/mirabelle_out" -A "try0" -A "sledgehammer[timeout=$SLEDGEHAMMER_TIMEOUT]" -T "$name_only" LemmaSledge
done


