use egg::*;
use log::error;
use std::str::FromStr;
use z3::ast::Int;
use z3::SatResult;
use z3::Solver;

use crate::language::get_z3_variables;
use crate::language::ModAnalysis;
use crate::language::ModIR;
use crate::language::ToZ3;

pub fn rules() -> Vec<Rewrite<ModIR, ModAnalysis>> {
    let mut rules = vec![
        // normal arithmetic
        rewrite!("add.commute";     "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("add.assoc";       "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rewrite!("mult.commute";    "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("mult.assoc";      "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),
        // identities
        rewrite!("mult_2";          "(* 2 ?a)" => "(+ ?a ?a)"),
        rewrite!("diff_self";       "(- ?a ?a)" => "0"),
        rewrite!("add_0";           "(+ 0 ?a)" => "?a"),
        rewrite!("mult_0";          "(* 0 ?a)" => "0"),
        rewrite!("mult_1";          "(* 1 ?a)" => "?a"),
        // ring identities?
        rewrite!("bw_pow_sum";      "(* (^ ?a (bw ?p ?b))
                                        (^ ?a (bw ?q ?c)))"     => "(^ ?a (+ (bw ?p ?b) (bw ?q ?c)))"),
        // conditional ring identities
        rewrite!("div_pow_join";    "(div (div ?a ?b) ?c)"      => "(div ?a (* ?b ?c))" if precondition(&["(> ?c 0)"])),
        rewrite!("div_mult_self";   "(div (+ ?a (* ?b ?c)) ?b)" => "(+ (div ?a ?b) ?c)" if precondition(&["(> ?b 0)"])),
        rewrite!("div_same";        "(div (* ?a ?b) ?a)"        => "?b"                 if precondition(&["(> ?a 0)"])),
        /////////////////////////
        //      MOD RELATED    //
        /////////////////////////
        rewrite!("bw_1"; "(bw ?p 1)" => "1"),
        rewrite!("bw_0"; "(bw ?p 0)" => "0"),
        // mod sum rewrite where outer bitwidth (p) is lower precision that inner (q)
        rewrite!("add_remove_prec";    "(bw ?p (+ (bw ?q ?a) ?b))"
                                    => "(bw ?p (+ ?a ?b))"
                                        if precondition(&["(>= ?q ?p)"])),
        rewrite!("add_eq_prec";        "(bw ?p (+ (bw ?p ?a) ?b))"
                                    => "(bw ?p (+ ?a ?b))"),
        // mod sum rewrite preserving full precision
        rewrite!("add_full_prec";      "(bw ?p (+ (bw ?q ?a) (bw ?r ?b)))"
                                    => "(+ (bw ?q ?a) (bw ?r ?b))"
                                    if precondition(&["(< ?q ?p)","(< ?r ?p)"])),
        // mod diff rewrite where outer bitwidth (p) is lower precision that inner (q)
        rewrite!("diff_left_rm_prec";  "(bw ?p (- (bw ?q ?a) ?b))"
                                    => "(bw ?p (- ?a ?b))"
                                        if precondition(&["(>= ?q ?p)"])),
        rewrite!("diff_left_eq_prec";  "(bw ?p (- (bw ?p ?a) ?b))"
                                    => "(bw ?p (- ?a ?b))"),
        rewrite!("diff_right_rm_prec"; "(bw ?p (- ?a (bw ?q ?b)))"
                                    => "(bw ?p (- ?a ?b))"
                                        if precondition(&["(>= ?q ?p)"])),
        rewrite!("diff_right_eq_prec"; "(bw ?p (- ?a (bw ?p ?b)))"
                                    => "(bw ?p (- ?a ?b))"),
        // precision preserving transform
        rewrite!("mul_full_prec";   "(bw ?r (* (bw ?q ?a) (bw ?p ?b)))"
                                 => "(* (bw ?q ?a) (bw ?p ?b))"
                                    if precondition(&["(>= ?r (+ ?p ?q))"])),
        // precision loss due to smaller outer mod
        rewrite!("mul_remove_prec"; "(bw ?q (* (bw ?p ?a) ?b))"
                                 => "(bw ?q (* ?a ?b))"
                                    if precondition(&["(>= ?p ?q)"])),
        rewrite!("mul_eq_prec";     "(bw ?q (* (bw ?q ?a) ?b))"
                                 => "(bw ?q (* ?a ?b))"),
        rewrite!("div_gte";         "(bw ?p (div (bw ?q ?a) ?b))"
                                 => "(div (bw ?q ?a) ?b)"
                                    if precondition(&["(>= ?p ?q)"])),
        rewrite!("reduce_mod";      "(bw ?q (bw ?p ?a))"
                                 => "(bw ?p ?a)"
                                    if precondition(&["(> ?q ?p)"])),
        rewrite!("reduce_mod_bis";  "(bw ?q (bw ?p ?a))"
                                 => "(bw ?q ?a)"
                                    if precondition(&["(> ?p ?q)"])),
        rewrite!("mod_eq";          "(bw ?p (bw ?p ?a))"
                                 => "(bw ?p ?a)"),
        rewrite!("mul_pow2";        "(bw ?s (* (bw ?p ?a) (^ 2 (bw ?q ?b))))"
                                 => "(* (bw ?p ?a) (^ 2 (bw ?q ?b)))"
                                    if precondition(&["(>= ?s (+ ?p (- (^ 2 ?q) 1)))"])),
        // shift operations
        rewrite!("shl_def"; "(<< (bw ?p ?a) (bw ?q ?b))" => "(* (bw ?p ?a) (^ 2 (bw ?q ?b)))"),
        rewrite!("shr_def"; "(>> (bw ?p ?a) (bw ?q ?b))" => "(div (bw ?p ?a) (^ 2 (bw ?q ?b)))"),
        // bitwise ring? properties
        rewrite!("or.commute";     "(or ?a ?b)" => "(or ?b ?a)"),
        rewrite!("or_assoc";       "(or (or ?a ?b) ?c)" => "(or ?a (or ?b ?c))"),
        rewrite!("and.commute";    "(and ?a ?b)" => "(and ?b ?a)"),
        rewrite!("and_assoc";      "(and (and ?a ?b) ?c)" => "(and ?a (and ?b ?c))"),
        // bitwise identities
        rewrite!("and_allones";     "(and (bw ?p ?a) (bw ?p -1))" => "(bw ?p ?a)"),
        rewrite!("or_allones";      "(or (bw ?p ?a) (bw ?p -1))" => "(bw ?p -1)"),
        rewrite!("xor_allones";     "(bw ?p (xor (bw ?p ?a) (bw ?p -1)))" => "(bw ?p (not (bw ?p ?a)))"),
        rewrite!("and_self";        "(and ?a ?a)" => "?a"),
        rewrite!("or_self";         "(or ?a ?a)" =>  "?a"),
        rewrite!("and_not_self";    "(and (bw ?p ?a) (bw ?p (not (bw ?p ?a))))" => "0"),
        rewrite!("or_not_self";     "(or (bw ?p ?a) (not (bw ?p ?a)))" => "(bw ?p -1)"),
        rewrite!("and_zero";        "(and ?a 0)" => "0"),
        rewrite!("or_zero";         "(or ?a 0)" => "?a"),
        // bitwise remove prec
        rewrite!("and_remove"; "(bw ?p (and (bw ?p ?a) (bw ?p ?b)))" => "(and (bw ?p ?a) (bw ?p ?b))"),
        rewrite!("or_remove";  "(bw ?p (or (bw ?p ?a) (bw ?p ?b)))" => "(or (bw ?p ?a) (bw ?p ?b))"),
        rewrite!("xor_remove"; "(bw ?p (xor (bw ?p ?a) (bw ?p ?b)))" => "(xor (bw ?p ?a) (bw ?p ?b))"),
        rewrite!("demorg_and"; "(bw ?p (not (and (bw ?p ?a) (bw ?p ?b))))" => "(bw ?p (or (bw ?p (not (bw ?p ?a))) (bw ?p (not (bw ?p ?b)))))"),
        rewrite!("demorg_or";  "(bw ?p (not (or (bw ?p ?a) (bw ?p ?b))))" => "(bw ?p (and (bw ?p (not (bw ?p ?a))) (bw ?p (not (bw ?p ?b)))))"),
    ];
    rules.extend(rewrite!("xor_and_or";      "(and (or (bw ?p ?a) (bw ?p ?b)) (or (bw ?p (not (bw ?p ?a))) (bw ?p (not (bw ?p ?b)))))" <=> "(xor (bw ?p ?a) (bw ?p ?b))"));
    // bitwise to arith
    rules.extend(rewrite!("neg_not"; "(- (bw ?p ?a))" <=> "(+ (not (bw ?p ?a)) 1)"));
    rules.extend(rewrite!("add_as_xor_and";
        "(+ (bw ?p ?a) (bw ?p ?b))"
            <=>
        "(+ (xor (bw ?p ?a) (bw ?p ?b)) (* 2 (and (bw ?p ?a) (bw ?p ?b))))"
    ));
    rules.extend(rewrite!("xor_as_or_and";
        "(xor (bw ?p ?a) (bw ?p ?b))"
        <=>
        "(- (or (bw ?p ?a) (bw ?p ?b)) (and (bw ?p ?a) (bw ?p ?b)))"
    ));
    rules.extend(rewrite!("and_distrib"; "(and ?a (or ?b ?c))" <=> "(or (and ?a ?b) (and ?a ?c))"));
    rules
        .extend(rewrite!("not_bw_not"; "(bw ?p (not (bw ?p (not (bw ?p ?a)))))" <=> "(bw ?p ?a)" ));

    rules.extend(rewrite!("not_0_allones"; "(bw ?p (not (bw ?p 0)))" <=> "(bw ?p -1)"));

    rules.extend(rewrite!("int_distrib"; "(* ?a (+ ?b ?c))" <=> "(+ (* ?a ?b) (* ?a ?c))"));
    rules.extend(rewrite!("Num.ring_1_class.mult_minus1"; "(- ?b)" <=> "(* -1 ?b)"));
    rules.extend(rewrite!("sub_to_neg"; "(- ?a ?b)" <=> "(+ ?a (* -1 ?b))"));
    // multliplication across the mod (this works because mod b implies mod 2^b)
    // c * (a mod b) = (c * a mod b * c)
    // rules.extend(rewrite!("mod-mul"; "(* (^ 2 ?e) (bw ?b ?c))" <=> "(bw (+ ?e ?b) (* (^ 2 ?e) ?c))"));
    rules.extend(rewrite!("gt-lt";      "(> ?a ?b)" <=> "(< ?b ?a)"));
    rules.extend(rewrite!("gte-lte";    "(>= ?a ?b)" <=> "(<= ?b ?a)"));
    // rules.extend();
    rules
}

fn apply_subst(
    expr: &RecExpr<ModIR>,
    subst: &Subst,
    egraph: &EGraph<ModIR, ModAnalysis>,
) -> RecExpr<ModIR> {
    match &expr[expr.root()] {
        ModIR::Var(s) => {
            return egraph.id_to_expr(*subst.get(Var::from_str(s.as_str()).unwrap()).unwrap());
        }
        other => {
            // traverse through each node and return another recexpr
            return other.join_recexprs(|id| {
                apply_subst(
                    &expr[id].build_recexpr(|id1| expr[id1].clone()),
                    subst,
                    egraph,
                )
            });
        }
    }
}

// given a list of preconditions, returns a function that checks that they are all satisfied
fn precondition(conds: &[&str]) -> impl Fn(&mut EGraph<ModIR, ModAnalysis>, Id, &Subst) -> bool {
    let cond_exprs: Vec<RecExpr<ModIR>> = conds.iter().map(|expr| expr.parse().unwrap()).collect();
    // look up the expr in the egraph then check that they are in the same eclass as the truth node
    move |egraph, _root, subst| {
        let mut res = true;
        for expr in &cond_exprs {
            let cond_subst: RecExpr<ModIR> = apply_subst(expr, subst, egraph);

            let mut is_true = egraph
                .lookup_expr_ids(&cond_subst)
                .and_then(|ids| {
                    egraph
                        .lookup(ModIR::Bool(true))
                        .and_then(|truth| Some(ids.iter().any(|&id| id == truth)))
                })
                .unwrap_or(false);
            if !is_true {
                is_true = infer_conditions(&cond_subst, egraph);
            }
            // println!(
            //     "{:#?} => {:#?}",
            //     expr.to_string(),
            //     cond_subst.to_string(),
            // );
            res &= is_true
        }
        res
    }
}

// Returns all RecExpr instances in the equivalence class of the True node
// For each distinct node pattern in the True e-class, returns the smallest representative RecExpr
// Excludes the Bool(true) node itself
pub fn get_true_exprs(egraph: &EGraph<ModIR, ModAnalysis>) -> Vec<RecExpr<ModIR>> {
    // First, lookup the True node in the egraph
    match egraph.lookup(ModIR::Bool(true)) {
        Some(true_id) => {
            // Get the equivalence class for the True node
            let eclass: &EClass<ModIR, <ModAnalysis as egg::Analysis<ModIR>>::Data> =
                &egraph[true_id];

            // For each node in the equivalence class, extract a representative expression
            eclass
                .nodes
                .iter()
                .filter(|node| {
                    // Exclude the Bool(true) node itself
                    !matches!(node, ModIR::Bool(true))
                })
                .map(|node: &ModIR| node.clone().join_recexprs(|id| egraph.id_to_expr(id)))
                .collect()
        }
        None => {
            // If there's no True node in the egraph, return an empty vector
            Vec::new()
        }
    }
}

// Given some condition that needs to be true, set it to be true based on some known truths
fn infer_conditions(condition: &RecExpr<ModIR>, egraph: &mut EGraph<ModIR, ModAnalysis>) -> bool {
    // println!("trying to infer truth for {}", condition.to_string());
    let mut truth_reason = match &condition[condition.root()] {
        ModIR::GT([a, b]) => match (&condition[*a], &condition[*b]) {
            (ModIR::Pow([_a, _b]), ModIR::Num(0)) => Some("simp"), // any expression of the form  (> (^ _ _) 0) is true, by simp
            _ => None,
        },
        _ => None,
    };

    if truth_reason.is_none() {
        let z3_cond_opt = condition.to_z3_cond();
        if let Some(z3_cond) = z3_cond_opt {
            // let vars = get_z3_variables(&z3_cond);
            let solver = Solver::new();
            for expr in get_true_exprs(egraph) {
                let z3_true_cond = expr.to_z3_cond();
                if let Some(cond) = z3_true_cond {
                    solver.assert(cond);
                } else {
                    error!("{} cannot be converted to z3", expr);
                }
            }
            solver.push();
            let is_sat = solver.check() == SatResult::Sat;
            solver.pop(1);
            assert!(
                is_sat,
                "Current precondition give empty set of widths: {}",
                solver.to_string()
            );
            // println!("True expressions: {:#?}", get_true_exprs(egraph));
            solver.assert(!z3_cond);
            if solver.check() == SatResult::Unsat {
                // println!("{}", solver.to_string());
                // println!("Solver result for {}: {:#?}", condition, solver.check());
                truth_reason = Some("z3")
            }
        } else {
            error!("condition {} cannot be converted to z3", condition);
        }
    }

    // add to the egraph in case the inference is successful
    if let Some(just) = truth_reason {
        println!("Inferred true condition: {} because of {}", condition, just);
        // println!("found new truth {} because {just}", condition.to_string());
        let cond_id = egraph.add_expr(condition);
        // get the truth id, it should exist within the egraph at this point
        let truth_id = egraph.lookup(ModIR::Bool(true)).unwrap();
        // quite hacky way to label where this truth value comes from
        // necessary for producing a theorem and justifying the inferred preconditions
        let union_reason = String::from("inferred_") + &String::from(just);
        egraph.union_trusted(truth_id, cond_id, union_reason);
    }
    return truth_reason.is_some();
}
