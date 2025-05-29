use crate::Symbol;
use egg::*;
use language::ModAnalysis;
use std::collections::HashSet;
use std::fs::File;
use std::io::Write;
use std::time::Duration;

mod dot_equiv;
mod extractor;
mod language;
mod rewrite_rules;
mod types;
mod utils;
use crate::extractor::EGraphCostFn;
use crate::language::ModIR;
use crate::rewrite_rules::rules;
use crate::utils::*;

pub use utils::check_isabelle_proof;
pub use utils::prepare_output_dir;

use std::path::{Path, PathBuf};
pub use types::EquivalenceString;
pub struct Equivalence {
    pub name: String,
    pub preconditions: Vec<RecExpr<ModIR>>,
    pub lhs: RecExpr<ModIR>,
    pub rhs: RecExpr<ModIR>,
    pub equiv: Option<bool>,
    bw_vars: HashSet<Symbol>,
    non_bw_vars: HashSet<Symbol>,
    proof: Option<Vec<egg::FlatTerm<ModIR>>>,
    inferred_truths: Option<Vec<(String, RecExpr<ModIR>)>>,
    runner: Runner<ModIR, ModAnalysis>,
}

impl Equivalence {
    pub fn new(name: &str, preconditions: &[&str], lhs: &str, rhs: &str) -> Self {
        // construct an equivalence struct
        // infer extra pre-conditions, mainly around which values need to be greater than 0
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

        let all_bw_vars: HashSet<Symbol> =
            unique_bitwidth_vars
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

        let precond_exprs: Vec<RecExpr<ModIR>> = preconditions
            .iter()
            .map(|&p| p.parse().unwrap())
            .chain(extra_preconditions)
            .collect::<Vec<_>>();

        let ret_self = Self {
            name: String::from(name),
            preconditions: precond_exprs,
            lhs: lhs_expr,
            rhs: rhs_expr,
            bw_vars: all_bw_vars,
            non_bw_vars: non_bw_vars,
            proof: None,
            inferred_truths: None,
            equiv: None,
            runner: Runner::<ModIR, ModAnalysis>::default()
                .with_explanations_enabled()
                .with_time_limit(Duration::from_secs(20)),
        };

        println!(
            "Created the following equivalence: \n{}\n =?\n{}\nwith the following conditions: {:}",
            ret_self.lhs.to_string(),
            ret_self.rhs.to_string(),
            ret_self.precond_str()
        );
        ret_self
    }

    fn precond_str(&self) -> String {
        self.preconditions
            .clone()
            .iter()
            .map(|e| format!("\"{}\"", print_infix(e, &self.bw_vars, false)))
            .collect::<Vec<_>>()
            .join(" and ")
    }

    pub fn find_equivalence(
        mut self,
        make_dot: Option<PathBuf>,
        save_out: Option<PathBuf>,
    ) -> Self {
        let (lhs_clone, rhs_clone) = (self.lhs.clone(), self.rhs.clone());
        let (lhs_for_dot, rhs_for_dot) = (self.lhs.clone(), self.rhs.clone());

        let make_dot: Option<PathBuf> = make_dot.map(|p| p.to_path_buf());

        // Set up the runner with optional dot file generation
        self.runner = self
            .runner
            .with_hook(move |runner| {
                if let Some(out_path) = &make_dot {
                    let iter_num = runner.iterations.len();
                    let dot = dot_equiv::make_dot(&runner.egraph, &lhs_for_dot, &rhs_for_dot);

                    let pdf_path = out_path.join(format!("iter_{}.pdf", iter_num));
                    let svg_path = out_path.join(format!("iter_{}.svg", iter_num));

                    dot.to_pdf(&pdf_path).unwrap();
                    dot.to_svg(&svg_path).unwrap();
                }

                if !runner.egraph.equivs(&lhs_for_dot, &rhs_for_dot).is_empty() {
                    Err("Found equivalence".into())
                } else {
                    Ok(())
                }
            })
            .with_expr(&lhs_clone)
            .with_expr(&rhs_clone);

        // Create the true node
        let truth_id = self.runner.egraph.add(ModIR::Bool(true));
        // Add the preconditions to the truth node of the egraph
        for precond in &self.preconditions {
            let p_id = self.runner.egraph.add_expr(precond);
            self.runner
                .egraph
                .union_trusted(truth_id, p_id, "preconditions");
        }

        let rewrite_rules = &rules();

        self.runner = self.runner.run(rewrite_rules);

        self.runner.print_report();
        self.inferred_truths = Some(get_inferred_truths(&self.runner.egraph));

        let equiv = !self.runner.egraph.equivs(&lhs_clone, &rhs_clone).is_empty();
        self.equiv = Some(equiv);

        let mut output_str = format!(
            "{} LHS and RHS are{}equivalent!\n",
            self.name,
            if equiv { " " } else { " not " }
        );

        self.proof = if equiv {
            let mut expl = self.runner.egraph.explain_equivalence(&self.lhs, &self.rhs);
            expl.check_proof(rewrite_rules);

            output_str += &expl.get_flat_string();
            Some(expl.make_flat_explanation().clone())
        } else {
            let cost_func = EGraphCostFn::new(&self.runner.egraph, &self.lhs, &self.rhs);
            // try to extract simplified representations
            let extractor = Extractor::new(&self.runner.egraph, cost_func);
            // need to look for the simplified version of the lhs and rhs expression
            let (_best_cost, best_lhs_expr) =
                extractor.find_best(self.runner.egraph.lookup_expr(&self.lhs).unwrap());
            let (_best_cost, best_rhs_expr) =
                extractor.find_best(self.runner.egraph.lookup_expr(&self.rhs).unwrap());

            output_str += &format!(
                "lhs simplified to:\n{}\nrhs simplified to:\n{}",
                best_lhs_expr.to_string(),
                best_rhs_expr.to_string()
            );
            None
        };

        let out_str = format!(
            "lhs:{}\nrhs:{}\nconditions:{}\n{}\n",
            self.lhs.to_string(),
            self.rhs.to_string(),
            self.precond_str(),
            output_str,
        );

        if let Some(path) = save_out {
            let mut file = File::create(path.join("explanation.txt")).unwrap();
            file.write(out_str.as_bytes()).unwrap();
        } else {
            print!("{}", out_str);
        }
        // equiv
        self
    }

    fn get_isabelle_proof(&self) -> Option<String> {
        // Returns None if there is no proof
        let flat_terms = if let Some(expl) = &self.proof {
            expl
        } else {
            return None;
        };

        assert!(!flat_terms.is_empty(), "Empty flat_terms vector");

        let mut prev_term = flat_terms[0].remove_rewrites();

        let extra_facts = self
            .inferred_truths
            .as_ref()
            .filter(|inf_t| !inf_t.is_empty())
            .map_or(String::from(""), |inf_t| {
                let (facts, note) = inf_t.iter().enumerate().fold(
                    (String::from(""), String::from("note inferred_facts =")),
                    |(acc, end), (i, (reason, expr))| {
                        (
                            acc + &format!(
                                "have fact_{i}: \"{}\" by {reason}\n",
                                print_infix(expr, &self.bw_vars, true)
                            ),
                            end + &format!("fact_{i} "),
                        )
                    },
                );
                facts + &note + "\n"
            });

        if flat_terms.len() > 2 {
            let mut proof_str = format!("proof -\n{extra_facts}");

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
                    print_infix(&term.remove_rewrites().get_recexpr(), &self.bw_vars, false);
                println!(
                    "{}: {} {} {} using {}",
                    i,
                    print_infix(&prev_term.get_recexpr(), &self.bw_vars, false),
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
                proof_str += &format!(
                    "    {prefix}have \"{lhs} = {term}\" {proof}\n",
                    prefix = if i == 0 { "" } else { "moreover " },
                    lhs = if i == 0 { "?lhs" } else { "..." },
                    term = next_term_str,
                    proof = proof_tactic
                );
                prev_term = term.remove_rewrites();
            }
            proof_str += "ultimately show ?thesis by argo\nqed\n";
            Some(proof_str)
        } else if flat_terms.len() == 2 {
            let (bw, fw) = flat_terms[1].get_rewrite();
            let rw = if bw.is_some() {
                bw.unwrap()
            } else {
                fw.unwrap()
            };
            Some(format!(
                "using that by (simp only: {rw_rule})\n",
                rw_rule = rw
            ))
        } else if flat_terms.len() == 1 {
            // if the length is one then the two are trivially equal
            Some(String::from("using that by simp\n"))
        } else {
            unreachable!("Something went wrong, proof with 0 length flat terms");
        }
    }

    pub fn to_isabelle(&self, path: &Path, use_lemmas: bool) {
        // Clean up theorem name
        let proof_name = &self.name;
        let proof_file_path = path.join(format!("{}.thy", proof_name));
        let mut proof_file = File::create(proof_file_path).unwrap();

        let nat_string = self
            .bw_vars
            .iter()
            .map(|i| i.to_string())
            .collect::<Vec<_>>()
            .join(" ");
        let int_string = self
            .non_bw_vars
            .iter()
            .map(|i| i.to_string())
            .collect::<Vec<_>>()
            .join(" ");

        proof_file
            .write(
                format!(
                    "theory {th_name}
    imports {imports}
begin
theorem {th_name}_th:
\"{lhs}={rhs}\" (is \"?lhs = ?rhs\")
if {preconditions}
for {nat_string} :: nat and {int_string} :: int\n",
                    imports = if use_lemmas {
                        "rewrite_lemmas"
                    } else {
                        "rewrite_defs"
                    },
                    th_name = proof_name,
                    lhs = print_infix(&self.lhs, &self.bw_vars, false),
                    rhs = print_infix(&self.rhs, &self.bw_vars, false),
                    preconditions = self.precond_str()
                )
                .as_bytes(),
            )
            .unwrap();

        if let Some(proof) = self.get_isabelle_proof() {
            proof_file.write(proof.as_bytes()).unwrap();
        } else {
            proof_file
                .write("proof -\n  show ?thesis sorry\nqed\n".as_bytes())
                .unwrap();
        }

        proof_file.write("\nend\n".as_bytes()).unwrap();
    }

    pub fn check_proof(&self, path: &Path) -> Result<(), std::io::Error> {
        return check_isabelle_proof(&vec![self.name.clone()], self.name.clone(), path);
    }
}
