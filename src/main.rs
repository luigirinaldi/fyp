// use serde::Deserialize;
use std::{
    collections::HashMap,
    fs::{self, File},
    io::Write,
    path::PathBuf,
};

use tqdm::tqdm;

use clap::Parser;
use egg::{Iteration, Report};
use hello_world::{check_isabelle_proof, prepare_output_dir, Equivalence, EquivalenceString};

#[derive(serde::Serialize)]
struct EquivRunnerInfo {
    summary: Report,
    iteration_info: Vec<Iteration<()>>,
}

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

    /// Store generated dot-files in this path (slows down proof generation)
    #[arg(long, value_name = "FILE")]
    dot_path: Option<PathBuf>,

    /// Store generated dot-files in this path
    #[arg(long, value_name = "FILE")]
    runner_stats: Option<PathBuf>,
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

    let checked_equivs: Vec<Equivalence> = tqdm(test_cases.iter())
        .map(|case| {
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
            }

            if let Some(th_path) = &cli.theorem_path {
                equiv.to_isabelle(th_path, !cli.def_only);
            }
            equiv
        })
        .collect();

    if !cli.skip_equiv {
        if let Some(info_path) = cli.runner_stats {
            if info_path.exists() {
                assert!(info_path.is_file(), "Runner stats path has to be a file");
            } else {
                prepare_output_dir(&info_path.parent().unwrap().to_path_buf(), false);
            }

            let stats: HashMap<String, EquivRunnerInfo> = checked_equivs
                .iter()
                .map(|e| {
                    (
                        e.name.clone(),
                        EquivRunnerInfo {
                            summary: e.runner.report(),
                            iteration_info: e.runner.iterations.clone(),
                        },
                    )
                })
                .collect();

            let mut file_out = File::create(&info_path)?;
            write!(file_out, "{}", serde_json::to_string(&stats).unwrap())?;
        }

        let (true_equivs, false_equivs): (Vec<_>, Vec<_>) = checked_equivs
            .into_iter()
            .partition(|e: &Equivalence| e.equiv.is_some_and(|x| x));

        let true_equivs_info = true_equivs
            .iter()
            .clone()
            .map(|eq| {
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
            .map(|eq| eq.name)
            .collect::<Vec<_>>();

        let false_equivs_info = false_equivs
            .iter()
            .clone()
            .map(|eq| {
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

            match check_isabelle_proof(
                &true_equivs_names,
                session_name.clone(),
                &cli.theorem_path.unwrap(),
            ) {
                Ok(wrong_proofs) => match wrong_proofs {
                    Some(hash) => {
                        let fails = &hash[&session_name.clone()];
                        eprintln!("The following equivalences were found to be correct but couldn't be verified:\n{}", fails.join("\n"));
                        Err(std::io::Error::other(
                            "Some equivalences couldn't be verified",
                        ))
                    }
                    None => Ok(()),
                },
                Err(e) => {
                    eprintln!("Error when checking isabelle proofs: {}", e);
                    Err(e)
                }
            }
        } else {
            Ok(())
        }
    } else {
        Ok(())
    }
}
