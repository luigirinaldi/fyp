use crate::language::validate_bwlang;
use crate::language::validate_precond;
use crate::language::ToZ3;
use crate::param_ir::compatible_conds;
use crate::param_ir::modir_cond_to_paramir_cond;
use crate::param_ir::modir_to_paramir;
use crate::param_ir::pbvvar_to_smt_string;
use crate::param_ir::rewrite_var_to_wvar;
use crate::param_ir::wvar_to_smt_string;
use crate::param_ir::ParamIR;
use crate::Symbol;
use egg::*;
use language::ModAnalysis;
use log::debug;
use std::collections::HashMap;
use std::collections::HashSet;
use std::time::Duration;
use z3::SatResult;
use z3::Solver;

use crate::param_ir::ParamUtils;
mod dot_equiv;
mod extractor;
mod language;
mod param_ir;
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

#[derive(Debug)]
pub struct Equivalence {
    pub name: String,
    pub preconditions: Vec<RecExpr<ModIR>>,
    pub width_gt_zero: Vec<RecExpr<ModIR>>,
    pub lhs: RecExpr<ModIR>,
    pub rhs: RecExpr<ModIR>,
    pub equiv: Option<bool>,
    pub runner: Runner<ModIR, ModAnalysis>,
    width_exprs: HashSet<RecExpr<ModIR>>,
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

impl Equivalence {
    pub fn new(name: &str, preconditions: &[&str], lhs: &str, rhs: &str) -> Self {
        // construct an equivalence struct
        // infer extra pre-conditions, mainly around which values need to be greater than 0
        let lhs_expr: RecExpr<ModIR> = lhs.parse().unwrap();
        let rhs_expr: RecExpr<ModIR> = rhs.parse().unwrap();

        let unique_bitwidth_expr: HashSet<_> = get_bitwidth_exprs(&lhs_expr)
            .iter()
            .chain(&get_bitwidth_exprs(&rhs_expr))
            .cloned()
            .collect();

        let all_vars = get_vars(&lhs_expr)
            .union(&get_vars(&rhs_expr))
            .cloned()
            .collect::<HashSet<_>>();

        let all_bw_vars: HashSet<Symbol> =
            unique_bitwidth_expr
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
        let extra_preconditions = unique_bitwidth_expr.iter().map(|e_old| {
            let mut e = e_old.clone();
            let root = e.root();
            let zero_id = e.add(ModIR::Num(0));
            // transform expr -> expr > 0
            e.add(ModIR::GT([root, zero_id]));
            e
        });

        let precond_exprs: Vec<RecExpr<ModIR>> =
            preconditions.iter().map(|&p| p.parse().unwrap()).collect();

        let ret_self = Self {
            name: String::from(name),
            preconditions: precond_exprs,
            width_gt_zero: extra_preconditions.collect(),
            lhs: lhs_expr,
            rhs: rhs_expr,
            width_exprs: unique_bitwidth_expr,
            bw_vars: all_bw_vars,
            non_bw_vars: non_bw_vars,
            proof: None,
            inferred_truths: None,
            equiv: None,
            runner: Runner::<ModIR, ModAnalysis>::default()
                .with_explanations_enabled()
                .with_time_limit(Duration::from_secs(10))
                .with_iter_limit(1000)
                .with_node_limit(200000)
                .with_scheduler(SimpleScheduler),
        };

        ret_self
    }

    pub fn precond_str(&self) -> String {
        self.preconditions
            .clone()
            .iter()
            .map(|e| format!("\"{}\"", print_infix(e, &self.bw_vars, false)))
            .collect::<Vec<_>>()
            .join(" and ")
    }

    pub fn reset_runner(mut self) -> Self {
        self.runner = Runner::<ModIR, ModAnalysis>::default()
            .with_explanations_enabled()
            .with_time_limit(Duration::from_secs(10))
            .with_iter_limit(1000)
            .with_node_limit(200000)
            .with_scheduler(SimpleScheduler);
        self
    }

    pub fn make_proof(mut self) -> Self {
        if let Some(equiv) = self.equiv {
            self.proof = if equiv {
                let mut expl = self.runner.egraph.explain_equivalence(&self.lhs, &self.rhs);
                expl.check_proof(&rules());

                Some(expl.make_flat_explanation().clone())
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

    fn get_isabelle_proof(&self) -> Option<String> {
        // Returns None if there is no proof
        let flat_terms = if let Some(expl) = &self.proof {
            expl
        } else {
            return None;
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
                let next_term_str =
                    print_infix(&term.remove_rewrites().get_recexpr(), &self.bw_vars, false);

                // Remove any '-rev' rewrites introduced by the double sided rewrite macro
                let rewrite_str = rw.to_string().replace("-rev", "");
                // Proof tactic based on the rewrite, by default use "simp only"
                // to show that the single step in the equational reasoning
                // is thanks to that rewrite
                let proof_tactic = match rewrite_str.as_str() {
                    // Using add to allow for simplication of constants
                    "constant_prop" => String::from("by (simp add: bw_def)"),
                    // use add instead of only to convert between nat type and int
                    val @ ("shl_def" | "shr_def") => format!("by (simp add: {val})"),
                    // need to use blast for diff_eq
                    val @ ("diff_left_eq_prec" | "diff_right_eq_prec") => {
                        format!("using that {val} by metis")
                    }
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

    pub fn to_isabelle(&self, use_lemmas: bool) -> String {
        // Clean up theorem name
        let proof_name = &self.name;
        let mut proof_string = String::new();

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
            imports = if use_lemmas {
                "rewrite_lemmas"
            } else {
                "rewrite_defs"
            },
            th_name = proof_name,
            lhs = print_infix(&self.lhs, &self.bw_vars, false),
            rhs = print_infix(&self.rhs, &self.bw_vars, false),
            preconditions = self.precond_str()
        ));

        if let Some(proof) = self.get_isabelle_proof() {
            proof_string.push_str(&proof);
        } else {
            proof_string.push_str("proof -\n  show ?thesis sorry\nqed\n");
        }

        proof_string.push_str("\nend\n");
        proof_string
    }

    pub fn check_proof(
        &self,
        path: &Path,
    ) -> Result<
        std::option::Option<HashMap<std::string::String, Vec<std::string::String>>>,
        std::io::Error,
    > {
        return check_isabelle_proof(&vec![self.name.clone()], self.name.clone(), path);
    }

    pub fn validate(&self) -> Result<(), String> {
        self.preconditions
            .iter()
            .map(|precond| validate_precond(precond, precond.root()))
            .collect::<Result<(), String>>()?;
        validate_bwlang(&self.rhs, self.rhs.root())?;
        validate_bwlang(&self.lhs, self.lhs.root())?;

        let solver = Solver::new();
        for expr in &self.width_exprs {
            solver.assert(expr.width_to_z3(expr.root())?.gt(0));
        }
        solver.push();
        // want to validate that all the bitwidths can be > 0
        if solver.check() != SatResult::Sat {
            let mut out_str = format!("The constraint on the width expressions all being greater than 0 produces an unsatisfiable set of widths:");
            for expr in &self.width_exprs {
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
        return Ok(());
    }

    /// Produces a vector of smtlib-pbv compatible strings
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
            let mut string_out: String = "(set-logic ALL)\n".to_string();

            for c in conds {
                string_out += &format!(";; {}\n", c.to_string());
            }

            let mut width_vars: HashSet<_> = lhs.get_width_var();
            width_vars.extend(rhs.get_width_var());
            let mut bitvector_vars = lhs.get_vars();
            bitvector_vars.extend(rhs.get_vars());
            // for p in preconds {
            //     assert!(
            //         p.get_width_var().is_subset(&width_vars),
            //         "precondition {} contains variables not present in the lhs and rhs, {:#?}, {:#?}",
            //         p.to_string(),
            //         p.get_width_var(),
            //         width_vars
            //     )
            // }
            for w in width_vars {
                string_out += &wvar_to_smt_string(&w);
                string_out += "\n";
            }
            for pbv in bitvector_vars {
                string_out += &pbvvar_to_smt_string(&pbv);
                string_out += "\n";
            }
            for cond in preconds {
                string_out += &format!("(assert {})", cond.to_string());
                string_out += "\n";
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
