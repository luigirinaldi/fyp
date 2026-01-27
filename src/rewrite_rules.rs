use egg::*;
use std::str::FromStr;

use crate::language::ModAnalysis;
use crate::language::ModIR;
use crate::language::ToZ3;

pub fn rules() -> Vec<Rewrite<ModIR, ModAnalysis>> {
    let mut rules = vec![
        // normal arithmetic
        rewrite!("isabelle-add.commute";     "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("isabelle-add.assoc";       "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rewrite!("isabelle-mult.commute";    "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("isabelle-mult.assoc";      "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),
        // identities
        rewrite!("diff_self";       "(- ?a ?a)" => "0"),
        rewrite!("add_0";           "(+ 0 ?a)" => "?a"),
        rewrite!("mult_0";          "(* 0 ?a)" => "0"),
        rewrite!("mult_1";          "(* 1 ?a)" => "?a"),
        rewrite!("mult_2";          "(* 2 ?a)" => "(+ ?a ?a)"),
        rewrite!("div_1";           "(div ?a 1)" => "?a"),
        // ring identities?
        rewrite!("bw_pow_sum";      "(* (^ ?a (bw ?p ?b))
                                        (^ ?a (bw ?q ?c)))"     => "(^ ?a (+ (bw ?p ?b) (bw ?q ?c)))"),
        // conditional ring identities
        rewrite!("div_pow_join";    "(div (div ?a ?b) ?c)"      => "(div ?a (* ?b ?c))" if precondition(&["(> ?c 0)"])),
        rewrite!("div_mult_self";   "(div (+ ?a (* ?b ?c)) ?b)" => "(+ (div ?a ?b) ?c)" if precondition(&["(> ?b 0)"])),
        rewrite!("div_same";        "(div (* ?a ?b) ?a)"        => "?b"                 if precondition(&["(> ?a 0)"])),
        // rewrite!("shift_mod"; "(bw ?q (>> (bw ?p ?a) ?b))" => "(bw ?q (>> ?a ?b))" if precondition(&["(>= (- ?p ?q) ?b)"])),
        // rewrite!("div-by-more"; "(div (bw 1 ?a) 2)" => "0"),
        /////////////////////////
        //      MOD RELATED    //
        /////////////////////////
        rewrite!("bw_1"; "(bw ?p 1)" => "1"),
        rewrite!("bw_0"; "(bw ?p 0)" => "0"),
        // mod sum rewrite where outer bitwidth (p) is lower precision that inner (q)
        rewrite!("add_remove_prec_left";    "(bw ?p (+ (bw ?q ?a) ?b))"
                                    => "(bw ?p (+ ?a ?b))"
                                        if precondition(&["(>= ?q ?p)"])),
        rewrite!("add_remove_prec_right";    "(bw ?p (+ ?a (bw ?q ?b)))"
                                    => "(bw ?p (+ ?a ?b))"
                                        if precondition(&["(>= ?q ?p)"])),
        rewrite!("add_eq_prec";        "(bw ?p (+ (bw ?p ?a) ?b))"
                                    => "(bw ?p (+ ?a ?b))"),
        // mod sum rewrite preserving full precision
        rewrite!("add_full_prec";      "(bw ?p (+ (bw ?q ?a) (bw ?r ?b)))"
                                    => "(+ (bw ?q ?a) (bw ?r ?b))"
                                    if precondition(&["(< ?q ?p)","(< ?r ?p)"])),
        // mod diff rewrite where outer bitwidth (p) is lower precision that inner (q)
        rewrite!("diff_left_remove_prec";  "(bw ?p (- (bw ?q ?a) ?b))"
                                    => "(bw ?p (- ?a ?b))"
                                        if precondition(&["(>= ?q ?p)"])),
        rewrite!("diff_left_eq_prec";  "(bw ?p (- (bw ?p ?a) ?b))"
                                    => "(bw ?p (- ?a ?b))"),
        rewrite!("diff_right_remove_prec"; "(bw ?p (- ?a (bw ?q ?b)))"
                                    => "(bw ?p (- ?a ?b))"
                                        if precondition(&["(>= ?q ?p)"])),
        rewrite!("diff_right_eq_prec"; "(bw ?p (- ?a (bw ?p ?b)))"
                                    => "(bw ?p (- ?a ?b))"),
        // precision preserving transform
        rewrite!("mul_full_prec";   "(bw ?r (* (bw ?q ?a) (bw ?p ?b)))"
                                 => "(* (bw ?q ?a) (bw ?p ?b))"
                                    if precondition(&["(>= ?r (+ ?p ?q))"])),
        rewrite!("mul_by_bit";      "(bw ?p (* (bw ?q ?a) (bw 1 ?b)))"
                                    => "(* (bw ?q ?a) (bw 1 ?b))"
                                    if precondition(&["(>= ?p ?q)"])),
        rewrite!("mul_by_bit_eq";      "(bw ?p (* (bw ?p ?a) (bw 1 ?b)))"
                                    => "(* (bw ?p ?a) (bw 1 ?b))"),
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
        // if not_already_bw("?p", "?b")),
        rewrite!("mod_eq";          "(bw ?p (bw ?p ?a))"
                                 => "(bw ?p ?a)"),
        rewrite!("mul_pow2";        "(bw ?s (* (bw ?p ?a) (^ 2 (bw ?q ?b))))"
                                 => "(* (bw ?p ?a) (^ 2 (bw ?q ?b)))"
                                    if precondition(&["(>= ?s (+ ?p (- (^ 2 ?q) 1)))"])),
        rewrite!("mod_prop_sum";    "(bw ?p (+ ?a ?b))"
                            => "(bw ?p (+ (bw ?p ?a) ?b))"
                            if not_already_bw("?p", "?a")),
        rewrite!("mod_prop_mul";    "(bw ?p (* ?a ?b))"
                            => "(bw ?p (* (bw ?p ?a) ?b))"
                            if not_already_bw("?p", "?a")),
        rewrite!("mod_prop_sub_left";    "(bw ?p (- ?a ?b))"
                            => "(bw ?p (- (bw ?p ?a) ?b))"
                            if not_already_bw("?p", "?a")),
        rewrite!("mod_prop_sub_right";    "(bw ?p (- ?a ?b))"
                            => "(bw ?p (- ?a (bw ?p ?b)))"
                            if not_already_bw("?p", "?a")),
        rewrite!("mod_prop_or";    "(bw ?p (or ?a ?b))"
                            => "(bw ?p (or (bw ?p ?a) ?b))"
                            if not_already_bw("?p", "?a")),
        rewrite!("mod_prop_and";    "(bw ?p (and ?a ?b))"
                            => "(bw ?p (and (bw ?p ?a) ?b))"
                            if not_already_bw("?p", "?a")),
        rewrite!("mod_prop_xor";    "(bw ?p (xor ?a ?b))"
                            => "(bw ?p (xor (bw ?p ?a) ?b))"
                            if not_already_bw("?p", "?a")),
        rewrite!("mod_prop_not";    "(bw ?p (not ?a))"
                            => "(bw ?p (not (bw ?p ?a)))"
                            if not_already_bw("?p", "?a")),
        rewrite!("mod_prop_neg";    "(bw ?p (- ?a))"
                            => "(bw ?p (- (bw ?p ?a)))"
                            if not_already_bw("?p", "?a")),
        // shift operations
        rewrite!("shl_def"; "(<< (bw ?p ?a) (bw ?q ?b))" => "(* (bw ?p ?a) (^ 2 (bw ?q ?b)))"),
        rewrite!("shr_def"; "(>> (bw ?p ?a) (bw ?q ?b))" => "(div (bw ?p ?a) (^ 2 (bw ?q ?b)))"),
        // rewrite!("shr_by_pos"; "(>> ?a ?b)" => "(div ?a (^ 2 ?b))" if precondition(&["(> ?b 0)"])),
        // bitwise ring? properties
        rewrite!("isabelle-or.commute";     "(or ?a ?b)" => "(or ?b ?a)"),
        rewrite!("isabelle-or_assoc";       "(or (or ?a ?b) ?c)" => "(or ?a (or ?b ?c))"),
        rewrite!("isabelle-and.commute";    "(and ?a ?b)" => "(and ?b ?a)"),
        rewrite!("isabelle-and_assoc";      "(and (and ?a ?b) ?c)" => "(and ?a (and ?b ?c))"),
        // bitwise identities
        rewrite!("and_allones";     "(and (bw ?p ?a) (bw ?p -1))" => "(bw ?p ?a)"),
        rewrite!("and_one";         "(and (bw ?p ?a) 1)" => "(bw 1 ?a)"),
        rewrite!("or_allones";      "(or (bw ?p ?a) (bw ?p -1))" => "(bw ?p -1)"),
        rewrite!("xor_allones";     "(bw ?p (xor (bw ?p ?a) (bw ?p -1)))" => "(bw ?p (not (bw ?p ?a)))"),
        // rewrite!("xor_one";         "(xor (bw ?p ?a) 1)" => "(+ (* (div (bw ?p ?a) 2) 2) (bw 1 (not (bw 1 ?a))))"),
        rewrite!("and_self";        "(and ?a ?a)" => "?a"),
        rewrite!("or_self";         "(or ?a ?a)" =>  "?a"),
        rewrite!("and_not_self";    "(and (bw ?p ?a) (bw ?p (not (bw ?p ?a))))" => "0"),
        rewrite!("or_not_self";     "(or (bw ?p ?a) (not (bw ?p ?a)))" => "(bw ?p -1)"),
        rewrite!("and_zero";        "(and ?a 0)" => "0"),
        rewrite!("or_zero";         "(or ?a 0)" => "?a"),
        // bitwise remove prec
        rewrite!("and_remove"; "(bw ?p (and (bw ?p ?a) (bw ?p ?b)))" => "(and (bw ?p ?a) (bw ?p ?b))"),
        rewrite!("and_remove_inner"; "(bw ?p (and (bw ?q ?a) ?b))" => "(bw ?p (and (bw ?p ?a) ?b))" if precondition(&["(> ?q ?p)"])),
        rewrite!("or_remove";  "(bw ?p (or (bw ?p ?a) (bw ?p ?b)))" => "(or (bw ?p ?a) (bw ?p ?b))"),
        rewrite!("xor_remove"; "(bw ?p (xor (bw ?p ?a) (bw ?p ?b)))" => "(xor (bw ?p ?a) (bw ?p ?b))"),
        rewrite!("demorg_and"; "(bw ?p (not (and (bw ?p ?a) (bw ?p ?b))))" => "(bw ?p (or (bw ?p (not (bw ?p ?a))) (bw ?p (not (bw ?p ?b)))))"),
        rewrite!("demorg_or";  "(bw ?p (not (or (bw ?p ?a) (bw ?p ?b))))" => "(bw ?p (and (bw ?p (not (bw ?p ?a))) (bw ?p (not (bw ?p ?b)))))"),
        rewrite!("sel_def"; "(bw ?p (sel ?cond ?a ?b))" => "(bw ?p (+ (* ?a (bw 1 ?cond)) (* ?b (bw 1 (not (bw 1 ?cond))))))"),
    ];
    rules.extend(rewrite!("xor_and_or";      "(and (or (bw ?p ?a) (bw ?p ?b)) (or (bw ?p (not (bw ?p ?a))) (bw ?p (not (bw ?p ?b)))))" <=> "(xor (bw ?p ?a) (bw ?p ?b))"));
    // bitwise to arith
    rules.extend(rewrite!("neg_not"; "(- (bw ?p ?a))" <=> "(+ (not (bw ?p ?a)) 1)"));
    rules.extend(rewrite!("add_as_xor_and";
        "(+ (bw ?p ?a) (bw ?q ?b))"
            <=>
        "(+ (xor (bw ?p ?a) (bw ?q ?b)) (* 2 (and (bw ?p ?a) (bw ?q ?b))))"
    ));
    rules.extend(rewrite!("xor_as_or_and";
        "(xor (bw ?p ?a) (bw ?q ?b))"
        <=>
        "(- (or (bw ?p ?a) (bw ?q ?b)) (and (bw ?p ?a) (bw ?q ?b)))"
    ));
    rules.extend(rewrite!("and_distrib"; "(and ?a (or ?b ?c))" <=> "(or (and ?a ?b) (and ?a ?c))"));
    rules
        .extend(rewrite!("not_bw_not"; "(bw ?p (not (bw ?p (not (bw ?p ?a)))))" <=> "(bw ?p ?a)" ));

    rules.extend(rewrite!("not_0_allones"; "(bw ?p (not (bw ?p 0)))" <=> "(bw ?p -1)"));

    rules.extend(rewrite!("int_distrib"; "(* ?a (+ ?b ?c))" <=> "(+ (* ?a ?b) (* ?a ?c))"));
    rules.extend(rewrite!("isabelle-Num.ring_1_class.mult_minus1"; "(- ?b)" <=> "(* -1 ?b)"));
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

            let known_value = egraph.lookup_expr_ids(&cond_subst).and_then(|ids| {
                let truth_id = egraph.lookup(ModIR::Bool(true));

                if let Some(truth) = truth_id {
                    if ids.iter().any(|&id| id == truth) {
                        return Some(true);
                    }
                }

                None
            });

            let is_true = match known_value {
                Some(value) => value,
                None => infer_conditions(&cond_subst, egraph),
            };
            if !is_true {
                return false;
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

fn not_already_bw(
    var_p: &str,
    var_x: &str,
) -> impl Fn(&mut EGraph<ModIR, ModAnalysis>, Id, &Subst) -> bool {
    let var_p = var_p.parse().unwrap();
    let var_x = var_x.parse().unwrap();

    move |egraph, _, subst| {
        let p = subst[var_p];
        let x = subst[var_x];

        // Get the eclass for x
        let x_eclass = &egraph[x];

        // Check if any node in x's eclass is (bw p ...)
        for node in &x_eclass.nodes {
            // Check if this node is a "bw" operation
            if let ModIR::Mod([bw_p, _]) = node {
                // Check if the first argument is in the same eclass as p
                if egraph.find(*bw_p) == egraph.find(p) {
                    return false; // Already has form (bw p ...), don't apply rewrite
                }
            }
        }

        true // Not in the form (bw p ...), allow the rewrite
    }
}
// Given some condition that needs to be true, set it to be true based on some known truths
fn infer_conditions(condition: &RecExpr<ModIR>, egraph: &mut EGraph<ModIR, ModAnalysis>) -> bool {
    let mut truth_reason = match &condition[condition.root()] {
        ModIR::GT([a, b]) => match (&condition[*a], &condition[*b]) {
            // any expression of the form  (> (^ _ _) 0) is true, by simp
            (ModIR::Pow([_a, _b]), ModIR::Num(0)) => Some("simp"),
            _ => None,
        },
        _ => None,
    };

    if truth_reason.is_none() {
        if let Ok(res) = condition.get_const_cond() {
            if res {
                // if the condition evaluates to true
                println!("Condition evaluted to true: {}", condition.to_string());
                truth_reason = Some("simp")
            } else {
                return false;
            }
        }
    }

    // add to the egraph in case the inference is successful
    if let Some(just) = truth_reason {
        // println!("Inferred true condition: {} because of {}", condition, just);
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
