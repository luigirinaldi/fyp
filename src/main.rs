// use serde::Deserialize;
use std::{fs, path::PathBuf};

use clap::Parser;
use hello_world::{check_isabelle_proof, prepare_output_dir, Equivalence, EquivalenceString};

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

    /// Run the isabelle proof check on the generated theorems
    #[arg(short, long, default_value = "false")]
    check_proofs: bool,

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

fn main() -> Result<(), std::io::Error> {
    let cli = Cli::parse();

    let path = cli.file_name;
    let data = fs::read_to_string(&path).expect("Failed to read input file");
    let test_cases: Vec<EquivalenceString> =
        serde_json::from_str(&data).expect("Failed to parse JSON");
    if let Some(th_path) = &cli.theorem_path {
        // Create the dir where all of the proofs will be stored, doing it here because it will delete previous
        prepare_output_dir(th_path, true);
    }

    // println!("{:#?}", test_cases);
    println!("Found {} test-cases", test_cases.len());

    let checked_equivs = test_cases.iter().map(|case| {
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

        let ret = if !cli.skip_equiv {
            // === Construct case-specific dot_path and expl_path ===
            let dot_path = cli.dot_path.as_ref().map(|base| {
                let path = base.join(&case.name);
                prepare_output_dir(&path, true);
                path
            });

            let expl_path = cli.expl_path.as_ref().map(|base| {
                let path = base.join(&case.name);
                prepare_output_dir(&path, true);
                path
            });
            equiv = equiv.find_equivalence(dot_path, expl_path);
            equiv.equiv
        } else {
            None
        };

        if let Some(th_path) = &cli.theorem_path {
            equiv.to_isabelle(th_path, !cli.def_only);
        }
        (ret, equiv)
    });

    let (true_equivs, false_equivs): (Vec<_>, Vec<_>) = checked_equivs
        .into_iter()
        .partition(|(res, _)| res.is_some_and(|x| x));

    let true_equivs_info = true_equivs
        .iter()
        .clone()
        .map(|(_res, eq)| {
            format!(
                "{} | {}s, {}",
                eq.name,
                eq.runner.report().total_time.to_string(),
                eq.runner.report().egraph_classes
            )
        })
        .collect::<Vec<_>>();

    let true_equivs_names = true_equivs
        .into_iter()
        .map(|(_res, eq)| eq.name)
        .collect::<Vec<_>>();

    let false_equivs_info = false_equivs
        .iter()
        .clone()
        .map(|(_res, eq)| {
            format!(
                "{} | {:?}, {}",
                eq.name,
                eq.runner.report().stop_reason,
                eq.runner.report().egraph_classes
            )
        })
        .collect::<Vec<_>>();

    println!(
        "The following equivalances were shown to be true:\n{}\nAnd the following to be false:\n{}",
        true_equivs_info.join("\n"),
        false_equivs_info.join("\n")
    );

    if cli.check_proofs && !true_equivs_names.is_empty() {
        assert!(
            cli.theorem_path.is_some(),
            "Theorem path is required to check the proofs"
        );
        assert!(!cli.def_only, "Can't check equivalences without the lemmas");

        let session_name = String::from(path.file_stem().unwrap().to_str().unwrap());

        return check_isabelle_proof(&true_equivs_names, session_name, &cli.theorem_path.unwrap());
    } else {
        Ok(())
    }
}
