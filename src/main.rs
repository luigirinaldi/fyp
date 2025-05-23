// use serde::Deserialize;
use std::{
    env, fs,
    path::{Path, PathBuf},
};

use clap::Parser;
use hello_world::{check_isabelle_proof, Equivalence, EquivalenceString};

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    /// Path to the JSON file containing the equalities to check
    file_name: PathBuf,

    /// Skip searching for equivalence
    #[arg(short, long, default_value = "false")]
    skip_equiv: bool,

    /// Only use the rewrite_defs, not the lemmas, when generating a theorem
    #[arg(short, long, default_value = "false")]
    def_only: bool,

    /// Store the generated theorem in this path
    #[arg(long, value_name = "FILE")]
    theorem_path: Option<PathBuf>,

    /// Store the explanation if it is found
    #[arg(long, value_name = "FILE")]
    expl_path: Option<PathBuf>,

    /// Store generated dot-files in this path
    #[arg(long, value_name = "FILE")]
    dot_path: Option<PathBuf>,
}

fn main() {
    let cli = Cli::parse();

    let path = cli.file_name;
    let data = fs::read_to_string(path).expect("Failed to read input file");
    let test_cases: Vec<EquivalenceString> =
        serde_json::from_str(&data).expect("Failed to parse JSON");

    println!("{:#?}", test_cases);
    for (_i, case) in test_cases.iter().enumerate() {
        let mut equiv = Equivalence::new(
            &case.name,
            &case
                .preconditions
                .iter()
                .map(|s| s.as_str())
                .collect::<Vec<&str>>(),
            &case.lhs,
            &case.rhs,
        );

        if !cli.skip_equiv {
            equiv.find_equivalence(cli.dot_path.clone(), cli.expl_path.clone());
        }

        if let Some(th_path) = &cli.theorem_path {
            equiv.to_isabelle(th_path, !cli.def_only);
        }
    }
}
