use crate::Symbol;
use egg::*;
use std::collections::HashSet;
use std::fs::File;
use std::io::{Error, Write};
use std::process::{Command, Stdio};
use std::time::Duration;

mod dot_equiv;
mod extractor;
mod language;
mod rewrite_rules;
mod utils;
use crate::extractor::EGraphCostFn;
use crate::language::ModIR;
use crate::rewrite_rules::rules;
use crate::utils::*;

use std::fs;
use std::path::Path;

// preconditions encoded as a list of conjunctions
pub fn check_equivalence(
    name_str: Option<&str>,
    preconditions: &[&str],
    lhs: &str,
    rhs: &str,
    skip_isabelle_check: Option<bool>,
) -> std::io::Result<()> {
    let name = name_str.unwrap_or("no-name-equivalence");
    let output_dir = String::from("target/") + name;
    let output_dir_for_graphs = output_dir.clone();

    if Path::new(&output_dir).exists() {
        fs::remove_dir_all(&output_dir).unwrap_or_else(|why| {
            println!("! {:?}", why.kind());
        });
    }

    fs::create_dir_all(&output_dir).unwrap_or_else(|why| {
        println!("! {:?}", why.kind());
    });

    let lhs_expr: RecExpr<ModIR> = lhs.parse().unwrap();
    let rhs_expr: RecExpr<ModIR> = rhs.parse().unwrap();

    let unique_bitwidth_vars: HashSet<_> = get_bitwidth_exprs(&lhs_expr)
        .iter()
        .chain(&get_bitwidth_exprs(&rhs_expr))
        .cloned()
        .collect();

    let all_vars = get_vars(&lhs_expr)
        .union(&get_vars(&rhs_expr))
        .cloned()
        .collect::<HashSet<_>>();

    let all_bw_vars = unique_bitwidth_vars
        .iter()
        .fold(HashSet::<_>::from([]), |mut vars, expr| {
            vars.extend(get_vars(expr));
            vars
        });

    let non_bw_vars = all_vars
        .iter()
        .filter(|item| !all_bw_vars.contains(item))
        .cloned()
        .collect::<HashSet<_>>();

    // Default conditions on the fact that all bitwidth variables must be strictly greater than 0
    let extra_preconditions = unique_bitwidth_vars.iter().map(|e_old| {
        let mut e = e_old.clone();
        let root = e.root();
        let zero_id = e.add(ModIR::Num(0));
        // transform expr -> expr > 0
        e.add(ModIR::GT([root, zero_id]));
        e
    });

    println!(
        "extra preconditions: {:#?}",
        extra_preconditions
            .clone()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
    );

    let precond_exprs: Vec<RecExpr<ModIR>> = preconditions
        .iter()
        .map(|&p| p.parse().unwrap())
        .chain(extra_preconditions)
        .collect::<Vec<_>>();

    let bw_vars_opt = all_bw_vars.iter().cloned().collect::<Vec<_>>();

    let precond_string = precond_exprs
        .clone()
        .iter()
        .map(|e| format!("\"{}\"", print_infix(e, &bw_vars_opt, false)))
        .collect::<Vec<_>>()
        .join(" and ");

    println!(
        "Checking \n{}\n =?\n{}\n given the following conditions: {:}",
        lhs_expr.to_string(),
        rhs_expr.to_string(),
        precond_string
    );

    let rhs_pattern = Pattern::from(&rhs_expr);

    let lhs_clone = lhs_expr.clone();
    let rhs_clone = rhs_expr.clone();

    let mut runner = Runner::default()
        .with_explanations_enabled()
        // .with_iter_limit(50)
        .with_time_limit(Duration::from_secs(20))
        .with_hook(move |runner| {
            dot_equiv::make_dot(&runner.egraph, &lhs_clone, &rhs_clone)
                .to_pdf(format!(
                    "{}/iter_{}.pdf",
                    output_dir_for_graphs,
                    runner.iterations.len()
                ))
                .unwrap();
            dot_equiv::make_dot(&runner.egraph, &lhs_clone, &rhs_clone)
                .to_svg(format!(
                    "{}/iter_{}.svg",
                    output_dir_for_graphs,
                    runner.iterations.len()
                ))
                .unwrap();

            if !runner.egraph.equivs(&lhs_clone, &rhs_clone).is_empty() {
                Err("Found equivalence".into())
            } else {
                Ok(())
            }
        })
        .with_expr(&lhs_expr)
        .with_expr(&rhs_expr);

    // add the preconditions to the truth values of the egraph
    let truth_id = runner.egraph.add(ModIR::Bool(true));
    for precond in &precond_exprs {
        let p_id = runner.egraph.add_expr(precond);
        runner.egraph.union_trusted(truth_id, p_id, "preconditions");
    }

    let rewrite_rules = &rules();

    let mut runner = runner.run(rewrite_rules);

    let equiv = !runner.egraph.equivs(&lhs_expr, &rhs_expr).is_empty();

    let output_file_path = output_dir.clone() + &String::from("/explanation.txt");
    let mut file = File::create(output_file_path)?;

    let output_str = format!(
        "{} LHS and RHS are{}equivalent!\n",
        name,
        if equiv { " " } else { " not " }
    );

    file.write(
        format!(
            "{}\nlhs:{}\nrhs:{}\nconditions:{}\n\n",
            output_str,
            lhs_expr.to_string(),
            rhs_expr.to_string(),
            precond_string
        )
        .as_bytes(),
    )?;
    print!("{}", output_str);

    let id = runner.egraph.find(*runner.roots.first().unwrap());

    if equiv {
        let matches = rhs_pattern.search_eclass(&runner.egraph, id).unwrap();
        let subst = matches.substs[0].clone();

        // runner = runner.with_explanation_length_optimization();
        let mut explained_short = runner.explain_matches(&lhs_expr, &rhs_pattern.ast, &subst);
        explained_short.check_proof(rewrite_rules);

        let flat_terms = explained_short.make_flat_explanation();
        // sanitize the name of the test to remove chars isabelle doesn't like
        let proof_name = name.replace("/", "_").replace(".rs", "");
        let proof_file_path = output_dir.clone() + &format!("/{}.thy", proof_name);
        let mut proof_file = File::create(proof_file_path)?;

        let nat_string = all_bw_vars
            .iter()
            .map(|i| i.to_string())
            .collect::<Vec<_>>()
            .join(" ");
        let int_string = non_bw_vars
            .iter()
            .map(|i| i.to_string())
            .collect::<Vec<_>>()
            .join(" ");

        let inf_t: Vec<(&str, RecExpr<ModIR>)> = get_inferred_truths(&runner.egraph);
        let extra_facts = if inf_t.len() > 0 {
            let (facts, note) = inf_t.iter().enumerate().fold(
                (String::from(""), String::from("note inferred_facts =")),
                |(acc, end), (i, (reason, expr))| {
                    (
                        acc + &format!(
                            "have fact_{i}: \"{}\" by {reason}\n",
                            print_infix(expr, &bw_vars_opt, true)
                        ),
                        end + &format!("fact_{i} "),
                    )
                },
            );
            facts + &note + "\n"
        } else {
            String::from("")
        };

        proof_file.write(
            format!(
                "theory {th_name}
    imports rewrite_lemmas
begin
theorem {th_name}_th:
\"{lhs}={rhs}\" (is \"?lhs = ?rhs\")
if {preconditions}
for {nat_string} :: nat and {int_string} :: int\n",
                th_name = proof_name,
                lhs = print_infix(&lhs_expr, &bw_vars_opt, false),
                rhs = print_infix(&rhs_expr, &bw_vars_opt, false),
                preconditions = precond_string
            )
            .as_bytes(),
        )?;

        let mut prev_term = flat_terms[0].remove_rewrites();

        if flat_terms.len() > 2 {
            proof_file.write(format!("proof -\n{extra_facts}").as_bytes())?;

            for (i, term) in flat_terms.iter().skip(1).enumerate() {
                let (bw, fw) = term.get_rewrite();
                let rw = if bw.is_some() {
                    bw.unwrap()
                } else {
                    fw.unwrap()
                };
                // assuming if one isn't defined the other one is
                let rw_dir = fw.is_some();
                let next_term_str =
                    print_infix(&term.remove_rewrites().get_recexpr(), &bw_vars_opt, false);
                println!(
                    "{}: {} {} {} using {}",
                    i,
                    print_infix(&prev_term.get_recexpr(), &bw_vars_opt, false),
                    if rw_dir { "->" } else { "<-" },
                    next_term_str,
                    rw
                );
                // Remove any '-rev' rewrites introduced by the double sided rewrite macro
                let rewrite_str = rw.to_string().replace("-rev", "");
                // Proof tactic based on the rewrite, by default use "simp only"
                // to show that the single step in the equational reasoning
                // is thanks to that rewrite
                let proof_tactic = match rewrite_str.as_str() {
                    // Using add to allow for simplication of constants
                    "constant_prop" => String::from("by (simp add: bw_def)"),
                    // use add instead of only to convert between nat type and int
                    "shl_def" => String::from("by (simp add: shl_def)"),
                    "shr_def" => String::from("by (simp add: shr_def)"),
                    val @ ("div_pow_join" | "div_mult_self" | "div_same") => {
                        format!("using that inferred_facts by (simp only: {val})")
                    }
                    other => format!("using that by (simp only: {})", other),
                };
                proof_file.write(
                    format!(
                        "    {prefix}have \"{lhs} = {term}\" {proof}\n",
                        prefix = if i == 0 { "" } else { "moreover " },
                        lhs = if i == 0 { "?lhs" } else { "..." },
                        term = next_term_str,
                        proof = proof_tactic
                    )
                    .as_bytes(),
                )?;
                prev_term = term.remove_rewrites();
            }
            proof_file.write("ultimately show ?thesis by argo\nqed\n".as_bytes())?;
        } else {
            let (bw, fw) = flat_terms[1].get_rewrite();
            let rw = if bw.is_some() {
                bw.unwrap()
            } else {
                fw.unwrap()
            };
            proof_file.write(
                format!("using that by (simp only: {rw_rule})\n", rw_rule = rw).as_bytes(),
            )?;
        }
        proof_file.write("end\n".as_bytes())?;

        explained_short.get_string_with_let();
        for s in explained_short.get_flat_strings() {
            println!("    {:#}", s);
        }
        println!("    {:#}", rhs_pattern.to_string());
        file.write(
            format!(
                "{}\n{}",
                explained_short.get_flat_string(),
                rhs_pattern.to_string()
            )
            .as_bytes(),
        )?;

        // 1. Copy rewrite lemma file
        if let Err(e) = fs::copy(
            "./proofs/rewrite_lemmas.thy",
            output_dir.clone() + "/rewrite_lemmas.thy",
        ) {
            eprintln!("Failed to copy file: {}", e);
            std::process::exit(1);
        }

        // 2. Create ROOT file in the destination directory
        let root_path = output_dir.clone() + "/ROOT";

        let mut file = match File::create(&root_path) {
            Ok(f) => f,
            Err(e) => {
                eprintln!("Failed to create ROOT file: {}", e);
                std::process::exit(1);
            }
        };

        let session_name = proof_name.clone() + "_proof";

        if let Err(e) = write!(
            file,
            "session {session_name} = HOL + theories\n  rewrite_lemmas\n  {proof_name}",
        ) {
            eprintln!("Failed to write to ROOT file: {}", e);
            std::process::exit(1);
        }

        // 3. Run bash command inside the destination directory
        if !skip_isabelle_check.unwrap_or(false) {
            println!("Checking proof with Isabelle");
            let output = Command::new("bash")
                .arg("-c")
                .arg(format!("isabelle build -v -d ./ -c {session_name}"))
                .current_dir(output_dir.clone())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output();

            match output {
                Ok(o) => {
                    if !o.status.success() {
                        eprintln!("Bash command exited with an error.");
                        Err(Error::other("proof couldn't be verified with isabelle"))
                    } else {
                        println!("Proof verified by Isabelle!");
                        Ok(())
                    }
                }
                Err(e) => {
                    eprintln!("Failed to run bash command: {}", e);
                    Err(e)
                }
            }
        } else {
            Ok(())
        }
    } else {
        let cost_func = EGraphCostFn::new(&runner.egraph, &lhs_expr, &rhs_expr);
        // try to extract simplified representations
        let extractor = Extractor::new(&runner.egraph, cost_func);
        // need to look for the simplified version of the lhs and rhs expression
        let (_best_cost, best_lhs_expr) =
            extractor.find_best(runner.egraph.lookup_expr(&lhs_expr).unwrap());
        let (_best_cost, best_rhs_expr) =
            extractor.find_best(runner.egraph.lookup_expr(&rhs_expr).unwrap());

        println!(
            "lhs simplified to:\n{}\nrhs simplified to:\n{}",
            best_lhs_expr.to_string(),
            best_rhs_expr.to_string()
        );
        Err(Error::other("equivalence not found"))
    }
}
