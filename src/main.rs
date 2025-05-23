// use serde::Deserialize;
use std::{
    env, fs,
    path::{Path, PathBuf},
};

use hello_world::{check_isabelle_proof, Equivalence, EquivalenceString};

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 2 {
        eprintln!("Usage: {} <path_to_test_file.json>", args[0]);
        std::process::exit(1);
    }

    let path = &args[1];
    let data = fs::read_to_string(path).expect("Failed to read input file");
    let test_cases: Vec<EquivalenceString> =
        serde_json::from_str(&data).expect("Failed to parse JSON");

    println!("{:#?}", test_cases);
    for (i, case) in test_cases.iter().enumerate() {
        Equivalence::new(case).find_equivalence(None, None);
    }

    let output_dir = PathBuf::from("./target/add_assoc_1");

    if Path::new(&output_dir).exists() {
        fs::remove_dir_all(&output_dir).unwrap_or_else(|why| {
            println!("! {:?}", why.kind());
        });
    }

    fs::create_dir_all(&output_dir).unwrap_or_else(|why| {
        println!("! {:?}", why.kind());
    });

    let proof_name = Equivalence::new(&EquivalenceString {
        name: String::from("add_assoc_1"),
        preconditions: vec![String::from("(>= q t)"), String::from("(>= u t)")],
        lhs: String::from("(bw t ( + (bw u (+ (bw p a) (bw r b))) (bw s c)))"),
        rhs: String::from("(bw t ( + (bw p a) (bw q (+ (bw r b) (bw s c)))))"),
    })
    .find_equivalence(None, None)
    .to_isabelle(&output_dir, true);

    check_isabelle_proof(proof_name, &output_dir).unwrap();
}
