#!/bin/sh

# # Check for proper usage
# if [ "$#" -ne 2 ]; then
#   echo "Usage: $0 SOURCE_DIR TARGET_DIR"
#   exit 1
# fi



SRC_DIR="./target/tests"
DEST_DIR="./test_proofs"

rm -rf "$DEST_DIR"

# Create the destination directory if it doesn't exist
mkdir -p "$DEST_DIR"

# Clear the list file if it exists
LIST_FILE="$DEST_DIR/ROOT"
> "$LIST_FILE"

cp ./proofs/rewrite_lemmas.thy "$DEST_DIR"

echo "session ProofCheck = HOL +
theories
  rewrite_lemmas" >> "$LIST_FILE"

# Traverse and copy .thy files
find "$SRC_DIR" -type f -name "*.thy" | while read -r file; do
  base_name=$(basename "$file")         # e.g., Example.thy
  name_only="${base_name%.thy}"         # e.g., Example

  # Copy to destination (may overwrite if names clash)
  cp "$file" "$DEST_DIR/$base_name"

  # Append name without extension to the list
  echo "  $name_only" >> "$LIST_FILE"
done

echo "Done. All .thy files copied to '$DEST_DIR'."
echo "File names listed in '$LIST_FILE'."


isabelle build -v -d "$DEST_DIR" -c ProofCheck