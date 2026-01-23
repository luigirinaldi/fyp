#!/usr/bin/env python3
"""
Standalone CLI tool to run a binary on a set of files and save results to CSV.
"""

import argparse
import csv
import json
import resource
import subprocess
import time
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed
from typing import Dict, List, Tuple

import psutil
from tqdm import tqdm

import shutil
import sys
from pathlib import Path
import subprocess


# HARDCODED BINARY PATH - Change this to your binary location
PARABIT_PATH = "../"
# ASSUMES PARABIT HAS BEEN COMPILED TO RELEASE MODE
BINARY_PATH = PARABIT_PATH + "target/release/parabit"

PROOF_PATH = PARABIT_PATH + "proofs/"

ISABELLE_DOCKER_IMAGE = "isabelle-docker:latest"


def set_memory_limit(bytes_limit: int):
    """Set memory limit for the current process."""
    resource.setrlimit(resource.RLIMIT_AS, (bytes_limit, bytes_limit))


def run_binary_on_file(
    input_file: Path,
    output_dir: Path,
    binary_path: str,
    timeout: int,
    memory_limit_gb: float,
    args: str | None,
) -> Tuple[str, bool, str, float, float]:
    """
    Run the binary on a single file with timeout and memory limits.
    Returns: (filename, success, last_error_line, time_taken, max_memory_mb)
    """
    base_name = input_file.name
    out_file = output_dir / f"{base_name}.out"
    err_file = output_dir / f"{base_name}.err"

    start_time = time.time()
    max_memory_mb = 0.0

    try:
        with open(out_file, "w") as stdout_f, open(err_file, "w") as stderr_f:
            # Start the process
            process = subprocess.Popen(
                [binary_path, str(input_file)] + args.split() if args else [binary_path, str(input_file)],
                stdout=stdout_f,
                stderr=stderr_f,
                preexec_fn=lambda: set_memory_limit(
                    int(memory_limit_gb * 1024 * 1024 * 1024)
                ),
            )

            # Monitor memory while process runs
            try:
                psutil_process = psutil.Process(process.pid)
                elapsed = 0.0
                sample_interval = 0.001

                while elapsed < timeout:
                    # Check if process is still running
                    if process.poll() is not None:
                        break

                    # Sample memory
                    try:
                        mem_info = psutil_process.memory_info()
                        current_memory_mb = mem_info.rss / (1024 * 1024)
                        max_memory_mb = max(max_memory_mb, current_memory_mb)
                    except (psutil.NoSuchProcess, psutil.AccessDenied):
                        break

                    time.sleep(sample_interval)
                    elapsed += sample_interval

                # Check for timeout
                if process.poll() is None:
                    process.kill()
                    process.wait()
                    time_taken = time.time() - start_time
                    last_err_line = f"TIMEOUT after {timeout}s"
                    return (base_name, False, last_err_line, time_taken, max_memory_mb)

            except psutil.NoSuchProcess:
                # Process ended very quickly
                process.wait()

        time_taken = time.time() - start_time
        success = process.returncode == 0

        # Read last error line if exists
        last_err_line = ""
        if err_file.exists():
            with open(err_file) as ef:
                lines = ef.readlines()
                if lines:
                    last_err_line = lines[-1].strip()

        # Check if memory limit was hit (common error)
        if not success and (
            "memory" in last_err_line.lower() or "allocation" in last_err_line.lower()
        ):
            last_err_line = f"MEMORY_LIMIT ({last_err_line})"

        return (base_name, success, last_err_line, time_taken, max_memory_mb)

    except Exception as e:
        time_taken = time.time() - start_time
        return (base_name, False, str(e), time_taken, max_memory_mb)

def extract_names_from_files(file_paths: list) -> Dict[str, str]:
    """
    Reads JSON files and extracts the 'name' key from each.
    
    Args:
        file_paths: List of file paths to JSON files
        
    Returns:
        Dictionary mapping filename to the 'name' value from the JSON
    """
    result = {}
    
    for file_path in file_paths:
        path = Path(file_path)
        try:
            with open(path, 'r') as f:
                data = json.load(f)
                if 'name' in data:
                    result[path.name] = data['name']
        except Exception as e:
            print(f"Error reading {file_path}: {e}")
    
    return result

def run_binary_parallel(
    input_dir: Path,
    output_dir: Path,
    max_workers: int,
    binary_path: str,
    timeout: int,
    memory_limit_gb: float,
    file_pattern: str,
    args: str,
) -> List[dict]:
    """
    Run the binary on all matching files in parallel with resource limits.
    Returns list of result dictionaries.
    """
    log_dir = output_dir / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)

    input_files = list(input_dir.glob(file_pattern))
    if not input_files:
        print(f" No files matching '{file_pattern}' found in {input_dir}")
        return []

    name_map = extract_names_from_files(input_files)

    print(
        f"\n= Running binary on {len(input_files)} files with {max_workers} parallel processes..."
    )
    print(f"   Binary: {binary_path}")
    print(f"   Timeout: {timeout}s, Memory limit: {memory_limit_gb}GB\n")

    results = []

    # Create a progress bar
    pbar = tqdm(total=len(input_files), desc="Processing files", position=0)

    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        future_to_file = {
            executor.submit(
                run_binary_on_file,
                f,
                log_dir,
                binary_path,
                timeout,
                memory_limit_gb,
                args,
            ): f
            for f in input_files
        }

        for future in as_completed(future_to_file):
            input_file = future_to_file[future]
            try:
                base_name, success, last_err_line, time_taken, max_memory_mb = (
                    future.result()
                )
                status = "SUCCESS" if success else "FAILED"
                timed_out = "TIMEOUT" in last_err_line
                results.append(
                    {
                        "file": base_name,
                        "problem_name": name_map[base_name],
                        "status": status,
                        "last_err_line": last_err_line,
                        "time_taken": time_taken,
                        "max_memory_mb": max_memory_mb,
                        "timed_out": timed_out,
                    }
                )
                # Update tqdm line with result
                if success:
                    pbar.write(
                        f" {base_name} ({time_taken:.2f}s, {max_memory_mb:.1f}MB)"
                    )
                else:
                    pbar.write(
                        f" {base_name} ({time_taken:.2f}s, {max_memory_mb:.1f}MB) - {last_err_line[:50]}"
                    )
            except Exception as e:
                pbar.write(f" Exception processing {input_file.name}: {e}")
                results.append(
                    {
                        "file": input_file.name,
                        "problem_name": name_map[input_file.name],
                        "status": "FAILED",
                        "last_err_line": str(e),
                        "time_taken": 0.0,
                        "max_memory_mb": 0.0,
                        "timed_out": False,
                    }
                )
            finally:
                pbar.update(1)

    pbar.close()
    return results


def save_results_to_csv(results: List[dict], output_file: Path):
    """Save results to a CSV file."""
    if not results:
        print("  No results to save")
        return

    fieldnames = [
        "file",
        "status",
        "time_taken",
        "max_memory_mb",
        "timed_out",
        "last_err_line",
        "problem_name",
    ]

    with open(output_file, "w", newline="") as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(results)

    print(f"\n Results saved to {output_file}")


def print_summary(results: List[dict]):
    """Print summary statistics."""
    if not results:
        return

    total = len(results)
    success_count = sum(1 for r in results if r["status"] == "SUCCESS")
    failed_count = total - success_count
    timeout_count = sum(1 for r in results if r["timed_out"])

    total_time = sum(r["time_taken"] for r in results)
    avg_time = total_time / total if total > 0 else 0
    max_time = max(r["time_taken"] for r in results) if results else 0

    avg_memory = sum(r["max_memory_mb"] for r in results) / total if total > 0 else 0
    max_memory = max(r["max_memory_mb"] for r in results) if results else 0

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Total files:        {total}")
    print(f"  Success:         {success_count} ({success_count / total * 100:.1f}%)")
    print(f"L Failed:          {failed_count} ({failed_count / total * 100:.1f}%)")
    print(f"  Timeouts:        {timeout_count}")
    print("\nTime statistics:")
    print(f"  Total time:       {total_time:.2f}s")
    print(f"  Average time:     {avg_time:.2f}s")
    print(f"  Max time:         {max_time:.2f}s")
    print("\nMemory statistics:")
    print(f"  Average memory:   {avg_memory:.1f}MB")
    print(f"  Max memory:       {max_memory:.1f}MB")
    print("=" * 60)


def count_lines(file_path):
    """
    Count the number of lines in a file.
    
    Args:
        file_path: Path to the file
        
    Returns:
        Number of lines in the file
    """
    with open(file_path, 'r') as f:
        return sum(1 for _ in f)

def run_isabelle(results : List[dict], isabelle_dir : Path):
    try:
        proof_path = Path(PROOF_PATH)
        
        for thy_file in proof_path.glob("*.thy"):
            shutil.copy(thy_file, isabelle_dir / thy_file.name)
            
    except Exception as e:
        print(f"Failed to copy .thy files: {e}", file=sys.stderr)
        sys.exit(1)

    theorems_to_check = []
    
    for r in results:
        if r['status'] == "SUCCESS":
            file_path = isabelle_dir / f"{r['problem_name']}.thy"
            num_lines = count_lines(file_path)
            if num_lines >= 4960:
                print("""
    ██     ██  █████  ██████  ███    ██ ██ ███    ██  ██████  
    ██     ██ ██   ██ ██   ██ ████   ██ ██ ████   ██ ██       
    ██  █  ██ ███████ ██████  ██ ██  ██ ██ ██ ██  ██ ██   ███ 
    ██ ███ ██ ██   ██ ██   ██ ██  ██ ██ ██ ██  ██ ██ ██    ██ 
     ███ ███  ██   ██ ██   ██ ██   ████ ██ ██   ████  ██████  
    """)
                print(f"Skipping {r['problem_name']} because {num_lines} are too many liens for isabelle")
                continue
            else:
                theorems_to_check.append(r['problem_name'])

    # 2. Create ROOT file in the destination directory
    root_path = isabelle_dir / "ROOT"
    try:
        with open(root_path, 'w') as file:
            file.write(f"session CheckProofs = HOL + theories\n  {"\n".join(theorems_to_check)}")
    except Exception as e:
        print(f"Failed to create or write to ROOT file: {e}", file=sys.stderr)
        sys.exit(1)

    # 3. Run bash command inside the destination directory
    print("Checking proof with Isabelle")
    try:
        result = subprocess.run(
             ["docker", "run", "-v", f"{isabelle_dir.absolute()}:/build_dir/", 
            ISABELLE_DOCKER_IMAGE, "build", "-v", "-d", "/build_dir/", "-c", "CheckProofs"],
            cwd=isabelle_dir,
            text=True
        )
        
        if not result.returncode == 0:
            raise ValueError(f"Isabelle proof check failed:\n{result.stdout}")
            # try:
            #     failing_theorems = find_failing_theories(result.stdout)
            #     return (True, failing_theorems)  # Returns Ok(Some(failing_theorems))
            # except Exception as e:
            #     print(f"Error while processing the logs: {e}", file=sys.stderr)
            #     raise e
        else:
            print("Proof verified by Isabelle!")
            return True
            
    except Exception as e:
        print(f"Failed to run bash command: {e}", file=sys.stderr)
        raise e

def main():
    parser = argparse.ArgumentParser(
        description="Run a binary on a set of files in parallel and save results to CSV"
    )
    parser.add_argument("input_dir", type=Path, help="Directory containing input files")
    parser.add_argument(
        "output_dir", type=Path, help="Directory to save output logs and CSV results"
    )
    parser.add_argument(
        "-j",
        "--jobs",
        type=int,
        default=4,
        help="Number of parallel processes (default: 4)",
    )
    parser.add_argument(
        "-t",
        "--timeout",
        type=int,
        default=300,
        help="Timeout per file in seconds (default: 300)",
    )
    parser.add_argument(
        "-m",
        "--memory",
        type=float,
        default=8.0,
        help="Memory limit per process in GB (default: 8.0)",
    )
    parser.add_argument(
        "-p",
        "--pattern",
        type=str,
        default="*.bwlang",
        help="File pattern to match (default: *.bwlang)",
    )
    parser.add_argument(
        "-o",
        "--csv-output",
        type=str,
        default="results.csv",
        help="Output CSV filename (default: results.csv)",
    )
    parser.add_argument(
        "--check-isabelle",
        default=False,
        action='store_true',
        help="Verify the generated equivalence by running it through Isabelle. This will override any arguments in 'extra-commands' (assumes a docker image is installed with isabelle)",
    )
    parser.add_argument(
        "--extra-commands",
        type=str,
        default=None,
        help="Commands to pass onto parabit",
    )

    args = parser.parse_args()

    # Validate inputs
    if not args.input_dir.exists():
        print(f"L Error: Input directory '{args.input_dir}' does not exist")
        return 1

    if not args.input_dir.is_dir():
        print(f"L Error: '{args.input_dir}' is not a directory")
        return 1

    # Create output directory
    args.output_dir.mkdir(parents=True, exist_ok=True)

    extra_parabit_args = args.extra_commands

    if args.check_isabelle:
        isabelle_dir = args.output_dir / "isabelle-check"
        isabelle_dir.mkdir()
        
        if extra_parabit_args != "":
            print("Warning: override extra parabit args")
        
        extra_parabit_args = f"get-proof --theorem-path {isabelle_dir}"

    # Run the binary on all files
    results = run_binary_parallel(
        input_dir=args.input_dir,
        output_dir=args.output_dir,
        max_workers=args.jobs,
        binary_path=BINARY_PATH,
        timeout=args.timeout,
        memory_limit_gb=args.memory,
        file_pattern=args.pattern,
        args=extra_parabit_args,
    )

    # Save results to CSV
    csv_path = args.output_dir / args.csv_output
    save_results_to_csv(results, csv_path)

    # Print summary
    print_summary(results)

    if args.check_isabelle:
        # Verify the generated results
        run_isabelle(results, isabelle_dir)

    return 0


if __name__ == "__main__":
    exit(main())
