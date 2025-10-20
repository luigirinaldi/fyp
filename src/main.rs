// use serde::Deserialize;
use std::{
    fs::{self, File},
    io::Write,
    path::PathBuf,
    time::Duration,
};

use env_logger;
use log::{debug, info, trace};

use std::time::Instant;

use std::option::Option;

use clap::Parser;
#[cfg(feature = "get-heap-info")]
use dhat;
use egg::{Iteration, Report};
use parabit::{prepare_output_dir, Equivalence, EquivalenceString};
#[cfg(feature = "get-heap-info")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

#[derive(serde::Serialize)]
struct EquivRunnerInfo {
    summary: Report,
    memory_footprint: Option<Duration>,
    crude_time: Option<f64>,
    iteration_info: Vec<Iteration<()>>,
}

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    /// Path to the file containing the equalitiy to check
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

    /// Verbosity level, feed a RUST_LOG compatible string
    #[arg(short, long, default_value = "parabit=info")]
    verbosity: String,
}

fn main() -> Result<(), std::io::Error> {
    let cli = Cli::parse();

    env_logger::Builder::new()
        .parse_filters(&cli.verbosity)
        .init();

    let path = cli.file_name;
    let data = fs::read_to_string(&path).expect("Failed to read input file");
    let equiv_str: EquivalenceString = serde_json::from_str(&data).expect("Failed to parse JSON");
    if let Some(th_path) = &cli.theorem_path {
        // Create the dir where all of the proofs will be stored, doing it here because it will delete previous
        prepare_output_dir(th_path, true);
    }

    let mut equiv: Equivalence = Equivalence::from(equiv_str);

    info!("Found equivalence: {}", equiv.name);
    debug!(
        "\nlhs:\t{}\nrhs:\t{}\nprecond:\t{}",
        equiv.lhs.to_string(),
        equiv.rhs.to_string(),
        equiv.precond_str()
    );
    trace!("{equiv:#?}");

    let stats = if !cli.skip_equiv {
        // === Construct case-specific dot_path and expl_path ===
        let dot_path = cli.dot_path.as_ref().map(|base| {
            let path = base.join(&equiv.name);
            prepare_output_dir(&path, true);
            path
        });

        let expl_path = cli.expl_path.as_ref().map(|base| {
            let path = base.join(&equiv.name);
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

    if !cli.skip_equiv {
        if let Some(info_path) = cli.runner_stats {
            if info_path.exists() {
                assert!(info_path.is_file(), "Runner stats path has to be a file");
            } else {
                prepare_output_dir(&info_path.parent().unwrap().to_path_buf(), false);
            }

            let stats = (
                equiv.name.clone(),
                EquivRunnerInfo {
                    summary: equiv.runner.report(),
                    memory_footprint: stats.0,
                    crude_time: stats.1.map(|d| d.as_secs_f64()),
                    iteration_info: equiv.runner.iterations.clone(),
                },
            );
            let mut file_out = File::create(&info_path)?;
            write!(file_out, "{}", serde_json::to_string(&stats).unwrap())?;
        }
    }
    Ok(())
}
