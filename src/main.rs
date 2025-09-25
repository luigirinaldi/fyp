// use serde::Deserialize;
use std::{
    collections::HashMap,
    fs::{self, File},
    io::Write,
    path::PathBuf,
    time::Duration,
};

use std::time::Instant;

use tqdm::tqdm;

use clap::Parser;
#[cfg(feature = "get-heap-info")]
use dhat;
use egg::{Iteration, Report};
use para_bit::{check_isabelle_proof, prepare_output_dir, Equivalence, EquivalenceString};
#[cfg(feature = "get-heap-info")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

#[derive(serde::Serialize)]
struct EquivRunnerInfo {
    summary: Report,
    memory_footprint: Option<u64>,
    crude_time: Option<f64>,
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

    /// Generate SMT2 PBV-Theory queries
    #[arg(long, default_value = "false")]
    smt2_convert: bool,
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

    let checked_equivs: Vec<(Equivalence, Option<u64>, Option<Duration>)> = tqdm(test_cases.iter())
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

            if cli.smt2_convert {
                if let Some(smt2) = equiv.to_smt2() {
                    println!("{}:\n{}\n", equiv.name, smt2);
                } else {
                    println!("conversion to smt2 pbv failed!\n{}", equiv.name)
                }
            }

            let stats = if !cli.skip_equiv {
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
                let mut total: Duration = Duration::from_millis(0);
                let mut count = 0;
                #[cfg(feature = "get-heap-info")]
                let mut bytes = 0;
                while total < Duration::from_secs(1) && count < 100 {
                    #[cfg(feature = "get-heap-info")]
                    let _profiler = dhat::Profiler::new_heap();
                    #[cfg(feature = "get-heap-info")]
                    let before_stats = dhat::HeapStats::get();
                    equiv = equiv.reset_runner();
                    let now = Instant::now();
                    {
                        equiv = equiv.find_equivalence(&dot_path, &expl_path);
                    }
                    let elapsed = now.elapsed();
                    #[cfg(feature = "get-heap-info")]
                    {
                        let after_stats = dhat::HeapStats::get();
                        bytes += after_stats.total_bytes - before_stats.total_bytes;
                    }
                    count += 1;
                    total += elapsed;
                }
                let average_dur = Some(total / count);
                #[cfg(feature = "get-heap-info")]
                {
                    let avg_bytes = bytes / u64::from(count);
                    (Some(avg_bytes), average_dur)
                }
                #[cfg(not(feature = "get-heap-info"))]
                (None, average_dur)
            } else {
                (None, None)
            };

            if let Some(th_path) = &cli.theorem_path {
                equiv.to_isabelle(th_path, !cli.def_only);
            }
            (equiv, stats.0, stats.1)
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
                .map(|(e, mem, dur)| {
                    (
                        e.name.clone(),
                        EquivRunnerInfo {
                            summary: e.runner.report(),
                            memory_footprint: mem.clone(),
                            crude_time: dur.map(|d| d.as_secs_f64()),
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
            .map(|(e, _m, _d)| e)
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
