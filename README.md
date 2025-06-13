```
Usage: para_bit [OPTIONS] <FILE_NAME>

Arguments:
  <FILE_NAME>  Path to the JSON file containing the equalities to check

Options:
  -s, --skip-equiv           Skip searching for equivalence
  -d, --def-only             Only use the rewrite_defs, not the lemmas, when generating a theorem
  -c, --check-proofs         Run the isabelle proof check on the generated theorems
      --theorem-path <FILE>  Store the generated theorem in this path
      --expl-path <FILE>     Store the explanation if it is found
      --dot-path <FILE>      Store generated dot-files in this path (slows down proof generation)
      --runner-stats <FILE>  Store statistics in this path
  -h, --help                 Print help
  -V, --version              Print version
```
