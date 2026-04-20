// use serde::Deserialize;
use std::{
    error::Error,
    fs::{self, File},
    io::Write,
    path::PathBuf,
    time::Duration,
};

use env_logger;
use log::{debug, info, trace};

use std::time::Instant;

use std::option::Option;

use clap::{Parser, Subcommand};
use egg::{Iteration, Report};
use parabit::{Equivalence, EquivalenceString};

#[derive(serde::Serialize)]
struct EquivRunnerInfo {
    summary: Report,
    crude_time: f64,
    iteration_info: Vec<Iteration<()>>,
}

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    /// Path to the file containing the equality to check
    file_name: PathBuf,

    #[command(subcommand)]
    command: Option<Command>,

    /// Verbosity level, feed a RUST_LOG compatible string
    /// For example: "parabit=debug" to get debug from parabit
    #[arg(short, long, default_value = "parabit=info")]
    verbosity: String,
}

#[derive(Subcommand)]
enum Command {
    /// Check if equality is true [default command]
    CheckEquals {
        /// Store the explanation if it is found
        #[arg(long, value_name = "FILE")]
        expl_path: Option<PathBuf>,

        /// Store generated dot-files in this path (slows down proof generation)
        #[arg(long, value_name = "FILE")]
        dot_path: Option<PathBuf>,

        /// Skip generating a proof if an equivalence is found
        /// (Sometimes proof generation takes considerably longer and more memory than the equivalence finding)
        #[arg(short, long, default_value = "false")]
        skip_proof: bool,
    },

    /// Run the equality checking while gathering runtime and memory footprint stats
    /// (need to compile with the get-heap-info feature flag for memory footprint)
    GetStats {
        /// Store stats in this path
        #[arg(long, value_name = "FILE")]
        stats_path: Option<PathBuf>,

        /// Maximum number of times to run the function to time it
        #[arg(long, default_value = "100")]
        max_times_run: u64,

        /// Maximum runtime for the average run in seconds
        #[arg(long, default_value = "1")]
        max_time: u64,
    },

    ValidateInput,

    /// Convert the bwlang file to SMT PBV
    #[cfg(feature = "smt-translate")]
    ToSmtPbv {
        /// Store the generated theorem in this directory
        #[arg(value_name = "DIR")]
        dest_path: PathBuf,
    },

    /// Convert to Isabelle
    GetProof {
        /// Store the generated theorem in this directory
        #[arg(long, value_name = "FILE")]
        theorem_path: Option<PathBuf>,

        /// Generates an empty theorem, skips searching for a proof
        #[arg(short, long, default_value = "false")]
        make_template: bool,
    },
}

fn main() -> Result<(), Box<dyn Error>> {
    let cli = Cli::parse();

    env_logger::Builder::new()
        .parse_filters(&cli.verbosity)
        .init();

    let path = cli.file_name;
    let data = fs::read_to_string(&path).expect("Failed to read input file");
    let equiv_str: EquivalenceString = serde_json::from_str(&data).expect("Failed to parse JSON");

    let mut equiv: Equivalence = Equivalence::from(equiv_str);
    info!("Running parabit on file: {}", equiv.name);
    equiv.validate()?;

    debug!(
        "\nlhs:\t{}\nrhs:\t{}\nprecond: {}",
        equiv.lhs.to_string(),
        equiv.rhs.to_string(),
        equiv.precond_str()
    );
    trace!("{equiv:#?}");
    let add_base =
        |path: &Option<PathBuf>, name: &String| path.as_ref().map(|base| base.join(name));

    // set the default command to be checking the equality with no options
    match &cli.command.unwrap_or(Command::CheckEquals {
        expl_path: None,
        dot_path: None,
        skip_proof: false,
    }) {
        Command::CheckEquals {
            expl_path,
            dot_path,
            skip_proof,
        } => {
            let name = equiv.name.clone();
            equiv = equiv.find_equivalence(&add_base(dot_path, &name));

            if !skip_proof {
                equiv = equiv.make_proof();
                let explanation_string = equiv.explanation_string();

                if let Some(path) = expl_path {
                    let mut file =
                        File::create(path.join(format!("{name} explanation.txt"))).unwrap();
                    file.write(explanation_string.as_bytes()).unwrap();
                } else {
                    println!("{}", explanation_string)
                }
            }

            if let Some(is_equiv) = equiv.equiv.clone() {
                if is_equiv {
                    return Ok(());
                } else {
                    return Err("Equivalence wasn't found".into());
                }
            } else {
                return Err("Something went wrong".into());
            }
        }
        Command::GetStats {
            stats_path,
            max_times_run,
            max_time,
        } => {
            let seconds: Duration = {
                let mut total: Duration = Duration::from_millis(0);
                let mut count = 0;
                while total < Duration::from_secs(*max_time) && count < *max_times_run {
                    equiv = equiv.reset_runner();
                    let now = Instant::now();
                    {
                        equiv = equiv.find_equivalence(&None);
                    }
                    let elapsed = now.elapsed();
                    if let Some(is_equiv) = &equiv.equiv {
                        if !is_equiv {
                            return Err("Equivalence wasn't found".into());
                        }
                    }
                    count += 1;
                    total += elapsed;
                }
                let average_dur = total.div_f64(count as f64);
                average_dur
            };

            match stats_path {
                Some(path) => {
                    assert!(path.exists(), "Path doesn't exist");
                    assert!(path.is_file(), "Runner stats path has to be a file");

                    let stats = (
                        equiv.name.clone(),
                        EquivRunnerInfo {
                            summary: equiv.runner.report(),
                            crude_time: seconds.as_secs_f64(),
                            iteration_info: equiv.runner.iterations.clone(),
                        },
                    );
                    let mut file_out = File::create(&path)?;
                    write!(file_out, "{}", serde_json::to_string(&stats).unwrap())?;
                }
                None => println!(
                    "Average Runtime: {}\nRunner report:\n{:#?}",
                    seconds.as_secs_f64(),
                    equiv.runner.report()
                ),
            };
            return Ok(());
        }
        Command::GetProof {
            theorem_path,
            make_template,
        } => {
            if !make_template {
                equiv = equiv.find_equivalence(&None).make_proof();
                if let Some(is_equiv) = &equiv.equiv {
                    if !is_equiv {
                        return Err("Equivalence wasn't found".into());
                    }
                }
            }

            match theorem_path {
                Some(path) => {
                    assert!(path.is_dir(), "Path must be a directory");
                    let proof_file_path = path.join(format!("{}.thy", equiv.name));
                    let mut proof_file = File::create(proof_file_path).unwrap();

                    proof_file.write(equiv.to_isabelle()?.as_bytes())?;
                    Ok(())
                }
                None => {
                    println!("{}", equiv.to_isabelle()?);
                    Ok(())
                }
            }
        }
        // input validation happends after the equiv is constructed, hence no need to do anything
        Command::ValidateInput => {
            equiv.validate()?;
            return Ok(());
        }
        #[cfg(feature = "smt-translate")]
        Command::ToSmtPbv { dest_path } => {
            if !dest_path.exists() {
                debug!("Creating directory {}", dest_path.to_string_lossy());
                std::fs::create_dir_all(&dest_path)?;
            }

            let probs = equiv.to_single_width_op()?;

            for (i, problem) in probs.into_iter().enumerate() {
                let mut file_path = dest_path.clone();
                file_path.push(format!("{}_{}.smt2", equiv.name, i));
                let mut file = std::fs::File::create(&file_path)?;
                let comment_header = format!(
                    ";; Equivalence Name: {}\n;; Preconditions: {}\n;; LHS: {}\n;; RHS: {}\n\n",
                    equiv.name,
                    equiv
                        .preconditions
                        .iter()
                        .map(|s| s.to_string())
                        .collect::<Vec<String>>()
                        .join(", "),
                    equiv.lhs,
                    equiv.rhs
                );
                std::io::Write::write_all(&mut file, comment_header.as_bytes())?;
                std::io::Write::write_all(&mut file, problem.as_bytes())?;
            }
            return Ok(());
        }
    }
}
