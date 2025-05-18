use crate::Symbol;
use egg::*;
use std::collections::HashSet;
use std::fs::File;
use std::io::{Error, Write};
use std::process::{Command, Stdio};
use std::str::FromStr;
use std::time::Duration;

mod dot_equiv;
mod extractor;
mod language;
use crate::extractor::EGraphCostFn;
use crate::language::ModAnalysis;
use crate::language::ModIR;

use std::fs;
use std::path::Path;

fn rules() -> Vec<Rewrite<ModIR, ModAnalysis>> {
    let mut rules = vec![
        // normal arithmetic
        rewrite!("add.commute";     "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("add.assoc";       "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rewrite!("mult.commute";    "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("mult.assoc";      "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),
        // identities
        rewrite!("diff_cancel"; "(- ?a ?a)" => "0"),
        rewrite!("add_0"; "(+ 0 ?a)" => "?a"),
        rewrite!("mult_0"; "(* 0 ?a)" => "0"),
        rewrite!("mult_1";  "(* 1 ?a)" => "?a"),
        // ring identities?
        rewrite!("bw_pow_sum";      "(* (^ ?a (bw ?p ?b)) 
                                        (^ ?a (bw ?q ?c)))"     => "(^ ?a (+ (bw ?p ?b) (bw ?q ?c)))"),
        rewrite!("div_pow_join";    "(div (div ?a ?b) ?c)"      => "(div ?a (* ?b ?c))"),
        // conditional ring identities
        rewrite!("div_mult_self";   "(div (+ ?a (* ?b ?c)) ?b)" => "(+ (div ?a ?b) ?c)" if precondition(&["(> ?b 0)"])),
        rewrite!("div_same";        "(div (* ?a ?b) ?a)"        => "?b"                 if precondition(&["(> ?a 0)"])),
        /////////////////////////
        //      MOD RELATED    //
        /////////////////////////

        // mod sum rewrite where outer bitwidth (p) is lower precision that inner (q)
        rewrite!("bw_1"; "(bw ?p 1)" => "1"),
        rewrite!("bw_0"; "(bw ?p 0)" => "0"),
        rewrite!("add_remove_prec";
            "(bw ?p (+ (bw ?q ?a) ?b))" => "(bw ?p (+ ?a ?b))"
            if precondition(&["(>= ?q ?p)"])),
        // mod sum rewrite preserving full precision
        rewrite!("add_full_prec";
            "(bw ?p (+ (bw ?q ?a) (bw ?r ?b)))" => "(+ (bw ?q ?a) (bw ?r ?b))"
            if precondition(&["(< ?q ?p)","(< ?r ?p)"])),
        // precision preserving transform
        rewrite!("mul_full_prec";
        "(bw ?r (* (bw ?q ?a) (bw ?p ?b)))" => "(* (bw ?q ?a) (bw ?p ?b))"
            if precondition(&["(>= ?r (+ ?p ?q))"])),
        // precision loss due to smaller outer mod
        rewrite!("mul_remove_prec";
            "(bw ?q (* (bw ?p ?a) ?b))" => "(bw ?q (* ?a ?b))"
            if precondition(&["(>= ?p ?q)"])),
        rewrite!("div_gte"; "(bw ?p (div (bw ?q ?a) ?b))" => "(div (bw ?q ?a) ?b)" if precondition(&["(>= ?p ?q)"])),
        rewrite!("reduce_mod"; "(bw ?q (bw ?p ?a))" => "(bw ?p a)" if precondition(&["(>= ?q ?p)"])),
        rewrite!("mul_pow2"; "(bw ?s (* (bw ?p ?a) (^ 2 (bw ?q ?b))))" => "(* (bw ?p ?a) (^ 2 (bw ?q ?b)))" if precondition(&["(>= ?s (+ ?p (- (^ 2 ?q) 1)))"])),
        // shift operations
        rewrite!("shl_def"; "(<< ?a ?b)" => "(* ?a (^ 2 ?b))"),
        rewrite!("shr_def"; "(>> ?a ?b)" => "(div ?a (^ 2 ?b))"),
    ];
    rules.extend(rewrite!("mult_2"; "(+ ?a ?a)" <=> "(* 2 ?a)"));
    rules.extend(rewrite!("int_distrib"; "(* ?a (+ ?b ?c))" <=> "(+ (* ?a ?b) (* ?a ?c))"));
    rules.extend(rewrite!("Num.ring_1_class.mult_minus1"; "(- ?b)" <=> "(* -1 ?b)"));
    rules.extend(rewrite!("sub_to_neg"; "(- ?a ?b)" <=> "(+ ?a (* -1 ?b))"));
    // multliplication across the mod (this works because mod b implies mod 2^b)
    // c * (a mod b) = (c * a mod b * c)
    // rules.extend(rewrite!("mod-mul"; "(* (^ 2 ?e) (bw ?b ?c))" <=> "(bw (+ ?e ?b) (* (^ 2 ?e) ?c))"));
    rules.extend(rewrite!("gt-lt"; "(> ?a ?b)" <=> "(< ?b ?a)"));
    rules.extend(rewrite!("gte-lte"; "(>= ?a ?b)" <=> "(<= ?b ?a)"));
    // rules.extend();
    rules
}

// given a list of preconditions, returns a function that checks that they are all satisfied
// TODO reimplement this using multipatterns https://github.com/luigirinaldi/fyp/issues/1
fn precondition(conds: &[&str]) -> impl Fn(&mut EGraph<ModIR, ModAnalysis>, Id, &Subst) -> bool {
    let cond_exprs: Vec<RecExpr<ModIR>> = conds.iter().map(|expr| expr.parse().unwrap()).collect();
    // look up the expr in the egraph then check that they are in the same eclass as the truth node
    move |egraph, _root, subst| {
        let mut res = true;
        for expr in &cond_exprs {
            fn copy_expr(
                expr: &RecExpr<ModIR>,
                subst: &Subst,
                egraph: &EGraph<ModIR, ModAnalysis>,
            ) -> RecExpr<ModIR> {
                match &expr[expr.root()] {
                    ModIR::Var(s) => {
                        return egraph
                            .id_to_expr(*subst.get(Var::from_str(s.as_str()).unwrap()).unwrap());
                    }
                    other => {
                        // traverse through each node and return another recexpr
                        return other.join_recexprs(|id| {
                            copy_expr(
                                &expr[id].build_recexpr(|id1| expr[id1].clone()),
                                subst,
                                egraph,
                            )
                        });
                    }
                }
            }

            let cond_subst: RecExpr<ModIR> = copy_expr(expr, subst, egraph);

            infer_conditions(&cond_subst, egraph);

            // println!(
            //     "{:#?} => {:#?}",
            //     expr.to_string(),
            //     cond_subst.to_string(),
            // );
            res &= egraph
                .lookup_expr_ids(&cond_subst)
                .and_then(|ids| {
                    egraph
                        .lookup(ModIR::Bool(true))
                        .and_then(|truth| Some(ids.iter().any(|&id| id == truth)))
                })
                .unwrap_or(false);
        }
        res
    }
}

// Given some condition that needs to be true, set it to be true based on some known truths
fn infer_conditions(condition: &RecExpr<ModIR>, egraph: &mut EGraph<ModIR, ModAnalysis>) {
    // println!("trying to infer truth for {}", condition.to_string());
    let truth_reason = match &condition[condition.root()] {
        ModIR::GT([a, b]) => match (&condition[*a], &condition[*b]) {
            (ModIR::Pow([_a, _b]), ModIR::Num(0)) => Some("simp"), // any expression of the form  (> (^ _ _) 0) is true, by simp
            _ => None,
        },
        _ => None,
    };

    // add to the egraph in case the inference is successful
    if let Some(just) = truth_reason {
        println!("found new truth {} because {just}", condition.to_string());
        let cond_id = egraph.add_expr(condition);
        // get the truth id, it should exist within the egraph at this point
        let truth_id = egraph.lookup(ModIR::Bool(true)).unwrap();
        // quite hacky way to label where this truth value comes from
        // necessary for producing a theorem and justifying the inferred preconditions
        let union_reason = String::from("inferred_") + &String::from(just);
        egraph.union_trusted(truth_id, cond_id, union_reason);
    }
}

fn get_inferred_truths(egraph: &EGraph<ModIR, ModAnalysis>) -> Vec<(&str, egg::RecExpr<ModIR>)> {
    let truth_id = egraph.lookup(ModIR::Bool(true)).unwrap();

    egraph
        .get_union_equalities()
        .iter()
        .cloned()
        .filter_map(move |(id1, id2, reason)| {
            let id = if id1 == truth_id {
                Some(id2)
            } else if id2 == truth_id {
                Some(id1)
            } else {
                None
            }?;

            if let Some(just) = reason.as_str().strip_prefix("inferred_") {
                let expr = egraph.id_to_expr(id);
                println!("found {id:?} with reason {}:\n{}", reason, expr);
                Some((just, expr))
            } else {
                None
            }
        })
        .collect::<Vec<_>>()
}

trait GetRewrite<L: Language> {
    fn get_rewrite(&self) -> (Option<Symbol>, Option<Symbol>);
}

impl<L: Language> GetRewrite<L> for FlatTerm<L> {
    fn get_rewrite(&self) -> (Option<Symbol>, Option<Symbol>) {
        if self.backward_rule.is_some() || self.forward_rule.is_some() {
            return (self.backward_rule, self.forward_rule);
        }
        let mut rewrites = self
            .children
            .iter()
            .map(|child| child.get_rewrite())
            .filter(|(back, front)| back.is_some() || front.is_some());

        let ret_val = rewrites.next();

        if let Some(next_rw) = rewrites.next() {
            println!(
                "Values left in rewrites {:#?} {:#?}",
                next_rw,
                rewrites.collect::<Vec<_>>()
            );
        }
        ret_val.unwrap_or((None, None))
    }
}

fn get_bitwidth_exprs(expr: &RecExpr<ModIR>) -> Vec<RecExpr<ModIR>> {
    let mut worklist = Vec::from([expr.root()]);
    let mut bw_vars: Vec<RecExpr<ModIR>> = [].to_vec();

    while !worklist.is_empty() {
        match &expr[worklist.pop().unwrap()] {
            ModIR::Mod([a, b]) => {
                bw_vars.push(expr[*a].build_recexpr(|id| expr[id].clone()));
                worklist.extend(expr[*b].children())
            }
            other => worklist.extend(other.children()),
        }
    }
    return bw_vars;
}

fn get_vars(expr: &RecExpr<ModIR>) -> HashSet<Symbol> {
    expr.iter()
        .filter_map(|node| {
            if let ModIR::Var(s) = node {
                Some(s.clone())
            } else {
                None
            }
        })
        .collect()
}

fn print_infix(expr: &RecExpr<ModIR>, nat_vars: &Vec<Symbol>, add_type_hint: bool) -> String {
    let get_child_str = |e: &RecExpr<ModIR>, id: &Id| -> String {
        print_infix(
            &e[*id].build_recexpr(|i| e[i].clone()),
            nat_vars,
            add_type_hint,
        )
    };

    fn is_nat_var(expr: &RecExpr<ModIR>, id: &Id, nat_vars: &Vec<Symbol>) -> bool {
        match &expr[*id] {
            ModIR::Var(symbol) => nat_vars.contains(&symbol),
            _ => false,
        }
    }

    match &expr[expr.root()] {
        val @ ModIR::Mod([a, b]) => {
            format!(
                "({} {} {})",
                val.to_string(),
                get_child_str(expr, a),
                get_child_str(expr, b)
            )
        }
        val @ ModIR::Pow([a, b]) if !is_nat_var(expr, b, nat_vars) => {
            format!(
                "({} {} nat ({}))",
                get_child_str(expr, a),
                val.to_string(),
                get_child_str(expr, b)
            )
        }
        ModIR::Num(num) if add_type_hint => format!("({num}::int)"),
        other => {
            if other.children().len() == 2 {
                format!(
                    "({} {} {})",
                    get_child_str(expr, &other.children()[0]),
                    other.to_string(),
                    get_child_str(expr, &other.children()[1])
                )
            } else if other.children().len() == 1 {
                format!(
                    "({} {})",
                    other.to_string(),
                    get_child_str(expr, &other.children()[0])
                )
            } else {
                other.to_string()
            }
        }
    }
}

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
                    val @ ("div_pow_join" | "div_mult_self") => {
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
