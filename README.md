```
Usage: parabit [OPTIONS] <FILE_NAME> [COMMAND]

Commands:
  check-equals  Check if equality is true [default command]
  get-stats     Run the equality checking while gathering runtime and memory footprint stats (need to compile with the get-heap-info feature flag for memory footprint)
  get-proof     Convert to Isabelle
  help          Print this message or the help of the given subcommand(s)

Arguments:
  <FILE_NAME>  Path to the file containing the equality to check

Options:
  -v, --verbosity <VERBOSITY>  Verbosity level, feed a RUST_LOG compatible string [default: parabit=info]
  -h, --help                   Print help
  -V, --version                Print version
```
