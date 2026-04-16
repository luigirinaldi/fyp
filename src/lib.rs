use crate::generated_matcher::rule_to_file;
use crate::language::validate_precond;
use crate::language::validate_term;
#[cfg(feature = "smt-translate")]
use crate::language::ToZ3;
use crate::utils::sanitise_vars;
use crate::Symbol;
use clap::error::Result;
use egg::*;
use language::ModAnalysis;
use log::debug;
use log::info;
use log::warn;
use std::collections::HashSet;
use std::time::Duration;
#[cfg(feature = "smt-translate")]
use z3::{SatResult, Solver};

mod dot_equiv;
mod extractor;
mod generated_matcher;
mod language;
#[cfg(feature = "smt-translate")]
mod param_ir;
#[cfg(feature = "smt-translate")]
use crate::param_ir::{
    compatible_conds, modir_cond_to_paramir_cond, modir_to_paramir, pbvvar_to_smt_string,
    rewrite_var_to_wvar, wvar_to_smt_string, ParamIR, ParamUtils,
};

mod rewrite_rules;
mod types;
mod utils;
use crate::extractor::EGraphCostFn;
use crate::language::ModIR;
use crate::rewrite_rules::rules;
use crate::utils::*;

use std::path::PathBuf;
pub use types::EquivalenceString;

#[derive(Debug)]
pub struct Equivalence {
    pub name: String,
    pub preconditions: Vec<RecExpr<ModIR>>,
    pub width_gt_zero: Vec<RecExpr<ModIR>>,
    pub lhs: RecExpr<ModIR>,
    pub rhs: RecExpr<ModIR>,
    pub equiv: Option<bool>,
    pub runner: Runner<ModIR, ModAnalysis>,
    bw_vars: HashSet<Symbol>,
    non_bw_vars: HashSet<Symbol>,
    proof: Option<Vec<egg::FlatTerm<ModIR>>>,
    inferred_truths: Option<Vec<(String, RecExpr<ModIR>)>>,
}

impl From<EquivalenceString> for Equivalence {
    fn from(item: EquivalenceString) -> Self {
        Equivalence::new(
            &item.name,
            &item
                .preconditions
                .iter()
                .map(|s| s.as_str())
                .collect::<Vec<&str>>(),
            &item.lhs,
            &item.rhs,
        )
    }
}

fn remove_redundant_proof(flat_explanation: FlatExplanation<ModIR>) -> FlatExplanation<ModIR> {
    log::info!("Reducing size");
    let mut expl: FlatExplanation<ModIR> = flat_explanation;
    loop {
        let prev_len = expl.len();
        let mut i: usize = 0;
        while i < expl.len() {
            let mut j: usize = i + 1;
            while j < expl.len() && expl[i] != expl[j] {
                j += 1;
            }
            if j < expl.len() {
                log::debug!(
                    "Found identical terms {i} {j}\n{}\n{}",
                    expl[i].remove_rewrites().get_string(),
                    expl[j].remove_rewrites().get_string()
                );
                expl.drain((i + 1)..=j);
                i = j
            } else {
                i += 1
            }
        }

        if prev_len == expl.len() {
            break;
        }
    }
    return expl;
}

fn sanitise_and_warn(inputs: &Vec<String>) -> Vec<RecExpr<ModIR>> {
    let exprs_in: Vec<RecExpr<ModIR>> = inputs.iter().map(|s| s.parse().unwrap()).collect();
    let exprs: Vec<RecExpr<ModIR>> = exprs_in.iter().map(|e| sanitise_vars(e)).collect();

    for (i, (expr_in, expr)) in exprs_in.iter().zip(exprs.iter()).enumerate() {
        let str_in = expr_in.to_string();
        let str_sanitised = expr.to_string();

        if str_sanitised != str_in {
            warn!(
                "Sanitised input expression {} from:\n{}\nto:\n{}",
                i, str_in, str_sanitised
            );
        }
    }

    exprs
}

impl Equivalence {
    pub fn new(name: &str, preconditions: &[&str], lhs: &str, rhs: &str) -> Self {
        // construct an equivalence struct
        // infer extra pre-conditions, mainly around which values need to be greater than 0
        let lhs_expr: RecExpr<ModIR> = sanitise_and_warn(&vec![lhs.to_string()])[0].clone();
        let rhs_expr: RecExpr<ModIR> = sanitise_and_warn(&vec![rhs.to_string()])[0].clone();

        let unique_bitwidth_expr: HashSet<_> = get_bitwidth_exprs(&lhs_expr)
            .iter()
            .chain(&get_bitwidth_exprs(&rhs_expr))
            .cloned()
            .collect();

        let all_vars = get_vars(&lhs_expr)
            .union(&get_vars(&rhs_expr))
            .cloned()
            .collect::<HashSet<_>>();

        let mut all_bw_vars: HashSet<Symbol> = get_width_vars(&lhs_expr);
        all_bw_vars.extend(&get_width_vars(&rhs_expr));

        let non_bw_vars = all_vars
            .iter()
            .filter(|item| !all_bw_vars.contains(item))
            .cloned()
            .collect::<HashSet<_>>();

        // Default conditions on the fact that all bitwidth variables must be strictly greater than 0
        let extra_preconditions = unique_bitwidth_expr.iter().map(|e_old| {
            let mut e = e_old.clone();
            let root = e.root();
            let zero_id = e.add(ModIR::Num(0));
            // transform expr -> expr > 0
            e.add(ModIR::GT([root, zero_id]));
            e
        });

        let precond_exprs: Vec<RecExpr<ModIR>> = sanitise_and_warn(
            &preconditions
                .iter()
                .map(|&p| p.parse().unwrap())
                .collect::<Vec<_>>(),
        );

        let ret_self = Self {
            name: String::from(name),
            preconditions: precond_exprs,
            width_gt_zero: extra_preconditions.collect(),
            lhs: lhs_expr,
            rhs: rhs_expr,
            bw_vars: all_bw_vars,
            non_bw_vars: non_bw_vars,
            proof: None,
            inferred_truths: None,
            equiv: None,
            runner: Runner::<ModIR, ModAnalysis>::default(),
        };
        ret_self.reset_runner()
    }

    pub fn precond_str(&self) -> String {
        self.preconditions
            .iter()
            .chain(&self.width_gt_zero)
            .map(|e| format!("\"{}\"", print_infix(e, &self.bw_vars, false).unwrap()))
            .collect::<Vec<_>>()
            .join(" and ")
    }

    pub fn reset_runner(mut self) -> Self {
        self.runner = Runner::<ModIR, ModAnalysis>::default()
            .with_explanations_enabled()
            .with_time_limit(Duration::from_secs(300))
            .with_iter_limit(2000)
            .with_node_limit(10000000)
            .with_scheduler(SimpleScheduler);
        self
    }

    pub fn make_proof(mut self) -> Self {
        if let Some(equiv) = self.equiv {
            self.proof = if equiv {
                let mut expl = self.runner.egraph.explain_equivalence(&self.lhs, &self.rhs);
                expl.check_proof(&rules());
                let flat_proof = expl.make_flat_explanation();
                let reduced = remove_redundant_proof(flat_proof.to_vec());
                log::debug!(
                    "Proof size reduced from {} to {}",
                    flat_proof.len(),
                    reduced.len()
                );
                let rules = rules();
                let mut checker = check_flat_proof(reduced.clone());
                // check proof after reduction
                checker(&rules);

                Some(reduced)
            } else {
                None
            };
        }
        self
    }

    pub fn explanation_string(&self) -> String {
        let mut output_str = if self.proof.is_some() {
            format!("{} LHS and RHS are equivalent!\n", self.name,)
        } else {
            format!(
                "{} Could not establish whether LHS and RHS are equivalent.\n",
                self.name
            )
        };
        if let Some(proof) = &self.proof {
            output_str += &proof
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join("\n");
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
            output_str += &format!("\n{:#?}", self.runner.report());
        }

        let out_str = format!(
            "lhs:{}\nrhs:{}\nconditions:{}\n{}\n",
            self.lhs.to_string(),
            self.rhs.to_string(),
            self.precond_str(),
            output_str,
        );

        debug!("{}", out_str);
        out_str
    }

    pub fn find_equivalence(mut self, make_dot: &Option<PathBuf>) -> Self {
        let (lhs_clone, rhs_clone) = (self.lhs.clone(), self.rhs.clone());
        let (lhs_for_dot, rhs_for_dot) = (self.lhs.clone(), self.rhs.clone());

        let make_dot: Option<PathBuf> = make_dot.as_ref().map(|p| p.to_path_buf());

        // Set up the runner with optional dot file generation
        self.runner = self
            .runner
            .with_hook(move |runner| {
                info!(
                    "Iteration {}: {} nodes, {} classes",
                    runner.iterations.len(),
                    runner.egraph.total_size(),
                    runner.egraph.number_of_classes()
                );
                if let Some(out_path) = &make_dot {
                    let iter_num = runner.iterations.len();
                    let dot = dot_equiv::make_dot(&runner.egraph, &lhs_for_dot, &rhs_for_dot);

                    // let pdf_path = out_path.join(format!("iter_{}.pdf", iter_num));
                    let svg_path = out_path.join(format!("iter_{}.svg", iter_num));

                    // dot.to_pdf(&pdf_path).unwrap();
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

        self.inferred_truths = Some(get_inferred_truths(&self.runner.egraph));

        let equiv = !self.runner.egraph.equivs(&lhs_clone, &rhs_clone).is_empty();
        self.equiv = Some(equiv);

        debug!("Equiv: {}", equiv);
        self
    }

    fn get_isabelle_proof(&self) -> Result<Option<(String, HashSet<String>)>, String> {
        // Returns None if there is no proof
        let flat_terms = if let Some(expl) = &self.proof {
            expl
        } else {
            return Ok(None);
        };

        assert!(!flat_terms.is_empty(), "Empty flat_terms vector");

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
                                print_infix(expr, &self.bw_vars, true).unwrap()
                            ),
                            end + &format!("fact_{i} "),
                        )
                    },
                );
                facts + &note + "\n"
            });

        let mut include_files: HashSet<String> = HashSet::<String>::new();

        fn process_rewrite(
            rw: String,
            include_files: &mut HashSet<String>,
        ) -> Result<String, String> {
            let rewrite_str = rw
                .replace("-rev", "") // remove the -rev introduced by two sided rewrites
                .replace("isabelle-", ""); // remove the isabelle- denoting a rule that uses isabelle definition

            if let Some(file) = rule_to_file(&rewrite_str) {
                include_files.insert(file.to_string());
                Ok(rewrite_str)
            } else if rw.find("isabelle-").is_some()
                || rw == "shl_def"
                || rw == "shr_def"
                || rw == "sel_def"
                || rw == "signed_def"
                || rw == "constant_prop"
            {
                // If the rewrite is either an isabelle native or a constant prop then we can ignore it
                Ok(rewrite_str)
            } else {
                Err(format!(
                    "Rewrite rule '{}' was not found in the lemma definitions.",
                    rewrite_str
                ))
            }
        }

        let proof_string_out = if flat_terms.len() > 2 {
            let mut proof_str = format!("proof -\n{extra_facts}");

            for (i, term) in flat_terms.iter().skip(1).enumerate() {
                let (bw, fw) = term.get_rewrite();
                let rw = if bw.is_some() {
                    bw.unwrap()
                } else {
                    fw.unwrap()
                };
                let next_term_str =
                    print_infix(&term.remove_rewrites().get_recexpr(), &self.bw_vars, false)?;

                let rewrite_str = process_rewrite(rw.to_string(), &mut include_files)?;

                // Proof tactic based on the rewrite, by default use "simp only"
                // to show that the single step in the equational reasoning is thanks to that rewrite
                let proof_tactic = match rewrite_str.as_str() {
                    // Using add to allow for simplication of constants
                    // Include `that` to give context about the conditions of the variables (needed to nat/int castings)
                    "constant_prop" => String::from("using that by (simp add: bw_def)"),
                    // use add instead of only to convert between nat type and int
                    val @ ("shl_def" | "shr_def" | "sel_def" | "signed_def") => {
                        format!("by (simp add: {val})")
                    }
                    // need to use blast for diff_eq
                    rule @ "mod_prop_sum" => {
                        format!("using that bw_def {rule} by (presburger ; fail | blast)")
                    }
                    val @ ("diff_left_eq_prec" | "diff_right_eq_prec") | val
                        if val.to_string().find("mod_prop").is_some() =>
                    {
                        format!("using that {val} by (blast; fail | metis)")
                    }
                    val @ ("div_pow_join" | "div_mult_self" | "div_same") => {
                        format!("using that inferred_facts by (simp only: {val})")
                    }
                    other => format!("using {rule} that by (simp ; fail | simp only: {rule}; fail | simp add: {rule}; fail | blast; fail | metis)", rule = {other}),
                };
                proof_str += &format!(
                    "    {prefix}have \"{lhs} = {term}\" {proof}\n",
                    prefix = if i == 0 { "" } else { "moreover " },
                    lhs = if i == 0 { "?lhs" } else { "..." },
                    term = next_term_str,
                    proof = proof_tactic
                );
            }
            proof_str += "ultimately show ?thesis by argo\nqed\n";
            proof_str
        } else if flat_terms.len() == 2 {
            let (bw, fw) = flat_terms[1].get_rewrite();
            let rw = if bw.is_some() {
                bw.unwrap()
            } else {
                fw.unwrap()
            };
            let rewrite_str = process_rewrite(rw.to_string(), &mut include_files)?;

            format!("using that by (simp only: {rewrite_str})\n",)
        } else if flat_terms.len() == 1 {
            // if the length is one then the two are trivially equal
            String::from("using that by simp\n")
        } else {
            unreachable!("Something went wrong, proof with 0 length flat terms");
        };

        Ok(Some((proof_string_out, include_files)))
    }

    pub fn to_isabelle(&self) -> Result<String, String> {
        // Clean up theorem name
        let proof_name = &self.name;
        let mut proof_string = String::new();

        let (proof_content, include_file_str) =
            if let Some((proof, files)) = self.get_isabelle_proof()? {
                let files_str: String = if files.len() == 0 {
                    "rewrite_defs".to_string()
                } else {
                    files.iter().fold(String::new(), |a, b| format!("{a} {b}"))
                };
                (proof, files_str)
            } else {
                (
                    "proof -\n  show ?thesis sorry\nqed\n".to_string(),
                    "rewrite_defs".to_string(),
                )
            };

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

        proof_string.push_str(&format!(
            "theory {th_name}
    imports {imports}
begin
theorem {th_name}_th:
\"{lhs}={rhs}\" (is \"?lhs = ?rhs\")
if {preconditions}
for {nat_string} :: nat and {int_string} :: int\n",
            imports = include_file_str,
            th_name = proof_name,
            lhs = print_infix(&self.lhs, &self.bw_vars, false)?,
            rhs = print_infix(&self.rhs, &self.bw_vars, false)?,
            preconditions = self.precond_str()
        ));

        proof_string.push_str(&proof_content);
        proof_string.push_str("\nend\n");
        Ok(proof_string)
    }

    pub fn validate(&self) -> Result<(), String> {
        self.preconditions
            .iter()
            .map(|precond| validate_precond(precond, precond.root()))
            .collect::<Result<(), String>>()?;
        validate_term(&self.rhs, self.rhs.root())?;
        validate_term(&self.lhs, self.lhs.root())?;

        // If smt-translate is enabled (which includes z3) then also
        // check that the input problem is not trivially true.
        #[cfg(feature = "smt-translate")]
        {
            let unique_bitwidth_expr: HashSet<_> = get_bitwidth_exprs(&self.lhs)
                .iter()
                .chain(&get_bitwidth_exprs(&self.rhs))
                .cloned()
                .collect();

            let solver = Solver::new();
            for expr in &unique_bitwidth_expr {
                solver.assert(expr.width_to_z3(expr.root())?.gt(0));
            }
            solver.push();
            // want to validate that all the bitwidths can be > 0
            if solver.check() != SatResult::Sat {
                let mut out_str = format!("The constraint on the width expressions all being greater than 0 produces an unsatisfiable set of widths:");
                for expr in &unique_bitwidth_expr {
                    out_str += " (";
                    out_str += &expr.to_string();
                    out_str += " > 0) and";
                }
                return Err(out_str);
            }
            solver.pop(1);

            for expr in &self.preconditions {
                solver.assert(expr.to_z3_cond()?);
            }
            // want to validate that given the provided preconditions the set of widths is satisfiable
            if solver.check() != SatResult::Sat {
                return Err(format!(
                    "The provided preconditions constrain the widths in an unsatisfiable way"
                ));
            }
        }
        return Ok(());
    }

    /// Produces a vector of smtlib-pbv compatible strings
    #[cfg(feature = "smt-translate")]
    pub fn to_single_width_op(&self) -> Result<Vec<String>, String> {
        let lhs_single_w = modir_to_paramir(&self.lhs, self.lhs.root())?;
        let rhs_single_w = modir_to_paramir(&self.rhs, self.rhs.root())?;
        let preconds_single_w: Vec<RecExpr<ParamIR>> = self
            .preconditions
            .iter()
            .map(|p| modir_cond_to_paramir_cond(p, p.root()))
            .collect::<Result<Vec<_>, String>>()?;
        println!(
            "Finished processing lhs and rhs, rhs has {} cases, lhs has {} cases",
            rhs_single_w.expr_out.len(),
            lhs_single_w.expr_out.len()
        );

        let valid_pairs: Vec<_> = lhs_single_w
            .expr_out
            .iter()
            .flat_map(|(conds_l, expr_l)| {
                rhs_single_w.expr_out.iter().filter_map({
                    let value = preconds_single_w.clone();
                    move |(conds_r, expr_r)| {
                        let conds = conds_r.iter().chain(conds_l).chain(&value);
                        if compatible_conds(conds).unwrap() {
                            Some((
                                conds_r.iter().chain(conds_l).collect::<Vec<_>>(),
                                expr_l.clone(),
                                expr_r.clone(),
                            ))
                        } else {
                            None
                        }
                    }
                })
            })
            .collect::<Vec<_>>();

        println!(
            "{} total combinations, {} valid ones",
            rhs_single_w.expr_out.len() * lhs_single_w.expr_out.len(),
            valid_pairs.len()
        );

        fn generate_smt_string(
            lhs: &RecExpr<ParamIR>,
            rhs: &RecExpr<ParamIR>,
            preconds: &[RecExpr<ParamIR>],
            conds: &Vec<&RecExpr<ParamIR>>,
        ) -> String {
            let mut string_out: String =
                "(set-logic ALL)\n;; Implied conditions on the bitvector width variables:\n"
                    .to_string();

            let implied_conds_in_string =
                conds.iter().map(|c| c.to_string()).collect::<HashSet<_>>();

            for c in &implied_conds_in_string {
                string_out += &format!(";; {c}\n");
            }

            let mut width_vars: HashSet<_> = lhs.get_width_var();
            width_vars.extend(rhs.get_width_var());
            let mut bitvector_vars = lhs.get_vars();
            bitvector_vars.extend(rhs.get_vars());
            // only keep those preconditions whose variables are present in the set of variables of the terms
            // because sometimes when constraining some variables may disappear
            let filtered_precs = preconds
                .into_iter()
                .filter(|p| p.get_width_var().is_subset(&width_vars));
            for w in &width_vars {
                string_out += &wvar_to_smt_string(&w);
                string_out += "\n";
            }
            for pbv in bitvector_vars {
                string_out += &pbvvar_to_smt_string(&pbv);
                string_out += "\n";
            }
            string_out += ";; User provided pre-conditions\n";

            for cond in filtered_precs {
                string_out += &format!("(assert {})", cond.to_string());
                string_out += "\n";
            }

            // remove conditions containing variables that don't appear, and convert to set of string (to avoid duplicates)
            let implied_conds_filtered = conds
                .iter()
                .filter(|c| c.get_width_var().is_subset(&width_vars))
                .map(|p| p.to_string())
                .collect::<HashSet<_>>();
            string_out += ";; Implied conditions\n";
            for c in implied_conds_filtered {
                string_out += &format!("(assert {c})\n");
            }
            string_out += "(assert (distinct\n    ";
            string_out += &rewrite_var_to_wvar(&lhs).to_string();
            string_out += "\n    ";
            string_out += &rewrite_var_to_wvar(&rhs).to_string();
            string_out += "\n))\n(check-sat)";
            string_out
        }

        Ok(valid_pairs
            .into_iter()
            .map(|(gen_cond, lhs, rhs)| {
                generate_smt_string(&lhs, &rhs, preconds_single_w.as_slice(), &gen_cond)
            })
            .collect())
    }
}
