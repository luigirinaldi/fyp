use std::fmt::{Debug, Error};
use std::hash::DefaultHasher;
use std::str::FromStr;
use std::sync::mpsc::RecvError;
use std::time::Duration;

use egg::*;
use num::rational::Ratio;
use num::{BigInt, BigRational, One};

mod dot_equiv;

use std::fs;
use std::path::Path;

type Num = num::BigRational;

define_language! {
    enum ModIR {
        "%" = Mod([Id; 2]), // mod operator to capture the bitwidth of a given sub-expression
        "@" = Sign([Id; 2]),
        // Arithmetic operators
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        // "/" = Div([Id; 2]),
        "~" = Neg(Id),
        ">>" = ShiftR([Id;2]),
        "<<" = ShiftL([Id;2]),
        // Operators to handle preconditions
        ">"  = GT([Id; 2]),
        ">=" = GTE([Id; 2]),
        "<"  = LT([Id; 2]),
        "<=" = LTE([Id; 2]),
        // truth value for preconditions
        Bool(bool),
        // Numbers
        Num(Num),
        // variables on which the operators operate
        Var(Symbol),
    }
}

#[derive(Default)]
struct ModAnalysis;

impl Analysis<ModIR> for ModAnalysis {
    type Data = Option<Num>;

    fn make(egraph: &mut EGraph<ModIR, Self>, enode: &ModIR) -> Self::Data {
        // first, we make a getter function that grabs the data for a given e-class id
        let get = |id: &Id| egraph[*id].data.as_ref();

        // now, we write the evaluator. Since the `Data` type is an `Option`, we
        // can use the `?` operator in Rust, which trys to unpack the
        // preceding optional value, "bailing" from the enclosing function if it's None
        match enode {
            ModIR::Num(n) => Some(n.clone()),
            ModIR::Neg(a) => Some(-(get(a)?.clone())),
            ModIR::Add([a, b]) => Some(get(a)? + get(b)?),
            ModIR::Sub([a, b]) => Some(get(a)? - get(b)?),
            ModIR::Mul([a, b]) => Some(get(a)? * get(b)?),
            ModIR::Var(_) => None,
            _ => None,
        }
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        match (to.as_mut(), from) {
            // Neither side is known to be a constant so there's nothing
            // to do when they merge.
            (None, None) => DidMerge(false, false),

            // Both sides are constants, so we should just make sure
            // they're the same.
            (Some(a), Some(b)) => {
                assert_eq!(a, &b, "bad merge!");
                DidMerge(false, false)
            }

            // The right side is a constant, so update `to` to be the same.
            (None, Some(x)) => {
                *to = Some(x);
                DidMerge(true, false)
            }

            // The left side is a constant and the right is not, so there's
            // nothing to do when they merge.
            (Some(_), None) => DidMerge(false, false),
        }
    }

    fn modify(egraph: &mut EGraph<ModIR, Self>, id: Id) {
        if let Some(n) = egraph[id].data.clone() {
            let id2 = egraph.add(ModIR::Num(n));
            egraph.union(id, id2);
        }
    }
}

#[rustfmt::skip]
fn rules() -> Vec<Rewrite<ModIR, ModAnalysis>> {
    let mut rules = vec![
        // normal arithmetic
        rewrite!("add-comm";    "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("add-assoc";   "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rewrite!("mul-comm";    "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("mul-assoc";   "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),

        rewrite!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
        rewrite!("canon-sub"; "(+ ?a (* -1 ?b))" => "(- ?a ?b)"),
        rewrite!("cancel-sub"; "(- ?a ?a)" => "0"),

        // rewrite!("minus1-distrib"; "(- ?a ?b)" => "(* -1 (- ?b ?a))"),

        // rewrite!("add2-mul"; "(+ ?a ?a)" => "(* 2 ?a)"),
        rewrite!("mul-add2"; "(* 2 ?a)"  => "(+ ?a ?a)"),

        rewrite!("zero-add"; "(+ ?a 0)" => "?a"),
        rewrite!("zero-mul"; "(* ?a 0)" => "0"),
        rewrite!("one-mul";  "(* ?a 1)" => "?a"),


        // rewrite!("add-distrib";     "(* ?a (+ ?b ?c))" s=> "(+ (* ?a ?b) (* ?a ?c))"),
        // rewrite!("add-distrib-r";   "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
        // rewrite!("mul-shift"; "(* ?a 2)" => "(<< ?a 1)"),

        // mod related
        // mod sum rewrite where outer bitwidth (p) is lower precision that inner (q)
        rewrite!("mod-sum";
            "(% ?p (+ (% ?q ?a) ?b))" => "(% ?p (+ ?a ?b))"
            if precondition(&["(>= ?q ?p)"])),
        rewrite!("mod-diff";
            "(% ?p (- (% ?q ?a) ?b))" => "(% ?p (- ?a ?b))"
            if precondition(&["(>= ?q ?p)"])),
        rewrite!("mod-diff-2";
            "(% ?p (- ?a (% ?q ?b)))" => "(% ?p (- ?a ?b))"
            if precondition(&["(>= ?q ?p)"])),
        // mod sum rewrite preserving full precision
        rewrite!("mod-sum-1";
            "(% ?p (+ (% ?q ?a) (% ?r ?b)))" => "(+ (% ?q ?a) (% ?r ?b))"
            if precondition(&["(< ?q ?p)","(< ?r ?p)"])),
        // precision preserving transform
        rewrite!("mod-mul-simp1";
            "(% ?r (* (% ?q ?a) (% ?p ?b)))" => "(* (% ?q ?a) (% ?p ?b))"
            if precondition(&["(> ?r (+ ?p ?q))"])),
        // precision loss due to smaller outer mod
        rewrite!("mod-mul-simp2";
            "(% ?q (* (% ?p ?a) ?b))" => "(% ?q (* ?a ?b))"
            if precondition(&["(>= ?p ?q)"])),

        // sign related
        rewrite!("signed";
            "(@ ?s (% ?bw ?a))" => "(- (* 2 (% (- ?bw 1) ?a)) (% ?bw ?a))"
            if precondition(&["(?s)"])
        )
    ];
    // rules.extend(rewrite!("lt_gt"; "(> ?a ?b)" <=> "(< ?b ?a)"));
    rules.extend(rewrite!("add-breakup"; "(+ (+ ?a ?b) (+ ?c ?d))" <=> "(+ ?a (+ ?b (+ ?c ?d)))"));
    //
    rules.extend(rewrite!("add-distrib"; "(* ?a (+ ?b ?c))" <=> "(+ (* ?a ?b) (* ?a ?c))"));
    rules.extend(rewrite!("sub-add"; "(- ?a ?b)" <=> "(+ ?a (~ ?b))"));
    rules.extend(rewrite!("sub-neg"; "(~ ?b)" <=> "(* -1 ?b)"));
    // multliplication across the mod (this works because mod b implies mod 2^b)
    rules.extend(rewrite!("mod-mul"; "(* 2 (% ?b ?c))" <=> "(% (+ 1 ?b) (* 2 ?c))"));
    rules.extend(rewrite!("gte-lt"; "(>= ?a ?b)" <=> "(< ?b ?a)"));
    rules
}

fn recursive_node_clone(
    egraph: &EGraph<ModIR, ModAnalysis>,
    root_id: &Id,
    new_expr: &mut RecExpr<ModIR>,
) -> Id {
    // let recurse = |a: &Id, b: &Id| -> [Id; 2] {
    //     let id_a = recursive_node_clone(egraph, a, new_expr);
    //     let id_b = recursive_node_clone(egraph, b, new_expr);
    //     [id_a, id_b]
    // };
    let root_node = egraph.id_to_node(*root_id);
    match root_node {
        ModIR::Var(s) => new_expr.add(ModIR::Var(*s)),
        ModIR::Mod([a, b]) => {
            let id_a = recursive_node_clone(egraph, a, new_expr);
            let id_b = recursive_node_clone(egraph, b, new_expr);

            new_expr.add(ModIR::Mod([id_a, id_b]))
        }
        ModIR::Sign([a, b]) => {
            let id_a = recursive_node_clone(egraph, a, new_expr);
            let id_b = recursive_node_clone(egraph, b, new_expr);

            new_expr.add(ModIR::Sign([id_a, id_b]))
        }
        ModIR::Add([a, b]) => {
            let id_a = recursive_node_clone(egraph, a, new_expr);
            let id_b = recursive_node_clone(egraph, b, new_expr);

            new_expr.add(ModIR::Add([id_a, id_b]))
        }
        ModIR::Sub([a, b]) => {
            let id_a = recursive_node_clone(egraph, a, new_expr);
            let id_b = recursive_node_clone(egraph, b, new_expr);

            new_expr.add(ModIR::Sub([id_a, id_b]))
        }
        ModIR::Mul([a, b]) => {
            let id_a = recursive_node_clone(egraph, a, new_expr);
            let id_b = recursive_node_clone(egraph, b, new_expr);

            new_expr.add(ModIR::Mul([id_a, id_b]))
        }
        ModIR::ShiftR([a, b]) => {
            let id_a = recursive_node_clone(egraph, a, new_expr);
            let id_b = recursive_node_clone(egraph, b, new_expr);

            new_expr.add(ModIR::ShiftR([id_a, id_b]))
        }
        ModIR::ShiftL([a, b]) => {
            let id_a = recursive_node_clone(egraph, a, new_expr);
            let id_b = recursive_node_clone(egraph, b, new_expr);

            new_expr.add(ModIR::ShiftL([id_a, id_b]))
        }
        ModIR::GT([a, b]) => {
            let id_a = recursive_node_clone(egraph, a, new_expr);
            let id_b = recursive_node_clone(egraph, b, new_expr);

            new_expr.add(ModIR::GT([id_a, id_b]))
        }
        ModIR::GTE([a, b]) => {
            let id_a = recursive_node_clone(egraph, a, new_expr);
            let id_b = recursive_node_clone(egraph, b, new_expr);

            new_expr.add(ModIR::GTE([id_a, id_b]))
        }
        ModIR::LT([a, b]) => {
            let id_a = recursive_node_clone(egraph, a, new_expr);
            let id_b = recursive_node_clone(egraph, b, new_expr);

            new_expr.add(ModIR::LT([id_a, id_b]))
        }
        ModIR::LTE([a, b]) => {
            let id_a = recursive_node_clone(egraph, a, new_expr);
            let id_b = recursive_node_clone(egraph, b, new_expr);

            new_expr.add(ModIR::LTE([id_a, id_b]))
        }
        ModIR::Bool(_bool) => new_expr.add(root_node.clone()),
        ModIR::Num(_num) => new_expr.add(root_node.clone()),
        ModIR::Neg(a) => {
            let id_a = recursive_node_clone(egraph, a, new_expr);

            new_expr.add(ModIR::Neg(id_a))
        }
    }
}

fn apply_subst(
    egraph: &EGraph<ModIR, ModAnalysis>,
    subst: &Subst,
    base_expr: &RecExpr<ModIR>,
    root_id: Id,
    new_expr: &mut RecExpr<ModIR>,
) -> Id {
    // disgusting
    let root_node = base_expr[root_id].clone();
    match root_node {
        ModIR::Var(s) => {
            let var = Var::from_str(s.as_str()).unwrap();
            // let new_node = egraph.id_to_node(*subst.get(var).unwrap());
            // print!("{:#?} ,", new_node);
            // new_expr.add(new_node.clone());
            recursive_node_clone(egraph, subst.get(var).unwrap(), new_expr)
        }
        ModIR::Mod([a, b]) => {
            let id_a = apply_subst(egraph, subst, base_expr, a, new_expr);
            let id_b = apply_subst(egraph, subst, base_expr, b, new_expr);
            new_expr.add(ModIR::Mod([id_a, id_b]))
        }
        ModIR::Sign([a, b]) => {
            let id_a = apply_subst(egraph, subst, base_expr, a, new_expr);
            let id_b = apply_subst(egraph, subst, base_expr, b, new_expr);
            new_expr.add(ModIR::Sign([id_a, id_b]))
        }
        ModIR::Neg(a) => {
            let id_a = apply_subst(egraph, subst, base_expr, a, new_expr);

            new_expr.add(ModIR::Neg(id_a))
        }
        ModIR::Add([a, b]) => {
            let id_a = apply_subst(egraph, subst, base_expr, a, new_expr);
            let id_b = apply_subst(egraph, subst, base_expr, b, new_expr);
            new_expr.add(ModIR::Add([id_a, id_b]))
        }
        ModIR::Sub([a, b]) => {
            let id_a = apply_subst(egraph, subst, base_expr, a, new_expr);
            let id_b = apply_subst(egraph, subst, base_expr, b, new_expr);
            new_expr.add(ModIR::Sub([id_a, id_b]))
        }
        ModIR::Mul([a, b]) => {
            let id_a = apply_subst(egraph, subst, base_expr, a, new_expr);
            let id_b = apply_subst(egraph, subst, base_expr, b, new_expr);
            new_expr.add(ModIR::Mul([id_a, id_b]))
        }
        ModIR::ShiftR([a, b]) => {
            let id_a = apply_subst(egraph, subst, base_expr, a, new_expr);
            let id_b = apply_subst(egraph, subst, base_expr, b, new_expr);
            new_expr.add(ModIR::ShiftR([id_a, id_b]))
        }
        ModIR::ShiftL([a, b]) => {
            let id_a = apply_subst(egraph, subst, base_expr, a, new_expr);
            let id_b = apply_subst(egraph, subst, base_expr, b, new_expr);
            new_expr.add(ModIR::ShiftL([id_a, id_b]))
        }
        ModIR::GT([a, b]) => {
            let id_a = apply_subst(egraph, subst, base_expr, a, new_expr);
            let id_b = apply_subst(egraph, subst, base_expr, b, new_expr);
            new_expr.add(ModIR::GT([id_a, id_b]))
        }
        ModIR::GTE([a, b]) => {
            let id_a = apply_subst(egraph, subst, base_expr, a, new_expr);
            let id_b = apply_subst(egraph, subst, base_expr, b, new_expr);
            new_expr.add(ModIR::GTE([id_a, id_b]))
        }
        ModIR::LT([a, b]) => {
            let id_a = apply_subst(egraph, subst, base_expr, a, new_expr);
            let id_b = apply_subst(egraph, subst, base_expr, b, new_expr);
            new_expr.add(ModIR::LT([id_a, id_b]))
        }
        ModIR::LTE([a, b]) => {
            let id_a = apply_subst(egraph, subst, base_expr, a, new_expr);
            let id_b = apply_subst(egraph, subst, base_expr, b, new_expr);
            new_expr.add(ModIR::LTE([id_a, id_b]))
        }
        ModIR::Bool(_bool) => new_expr.add(root_node.clone()),
        ModIR::Num(num) => new_expr.add(ModIR::Num(num)),
    }
}

// given a list of preconditions, returns a function that checks that they are all satisfied
fn precondition(conds: &[&str]) -> impl Fn(&mut EGraph<ModIR, ModAnalysis>, Id, &Subst) -> bool {
    let cond_exprs: Vec<RecExpr<ModIR>> = conds.iter().map(|expr| expr.parse().unwrap()).collect();
    // look up the expr in the egraph then check that they are in the same eclass as the truth node
    move |egraph, _root, subst| {
        let mut res = true;
        for expr in &cond_exprs {
            let mut cond_subst: RecExpr<ModIR> = RecExpr::default();

            apply_subst(egraph, subst, expr, expr.root(), &mut cond_subst);

            // println!(
            //     "{:#?} => {:#?} {:#?}",
            //     expr.to_string(),
            //     cond_subst.to_string(),
            //     cond_subst
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

// preconditions encoded as a list of conjunctions
fn check_equivalence(name_str: Option<&str>, preconditions: &[&str], lhs: &str, rhs: &str) {
    let name = name_str.unwrap_or("no-name-check");
    let dot_output_dir = String::from("target/") + name;

    if Path::new(&dot_output_dir).exists() {
        fs::remove_dir_all(&dot_output_dir).unwrap_or_else(|why| {
            println!("! {:?}", why.kind());
        });
    }

    fs::create_dir_all(&dot_output_dir).unwrap_or_else(|why| {
        println!("! {:?}", why.kind());
    });

    let precond_exprs: Vec<RecExpr<ModIR>> =
        preconditions.iter().map(|&p| p.parse().unwrap()).collect();

    let lhs_expr: RecExpr<ModIR> = lhs.parse().unwrap();
    let rhs_expr: RecExpr<ModIR> = rhs.parse().unwrap();

    println!(
        "Checking \n{}\n =?\n{}\n given the following conditions: {:?}",
        lhs_expr.to_string(),
        rhs_expr.to_string(),
        preconditions
    );

    let _lhs_pattern = Pattern::from(&lhs_expr);
    let rhs_pattern = Pattern::from(&rhs_expr);

    let lhs_clone = lhs_expr.clone();
    let rhs_clone = rhs_expr.clone();

    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_iter_limit(50)
        .with_time_limit(Duration::from_secs(60))
        .with_hook(move |runner| {
            // dot_equiv::make_dot(&runner.egraph, &lhs_clone, &rhs_clone)
            //     .to_dot(format!(
            //         "{}/iter_{}.dot",
            //         dot_output_dir,
            //         runner.iterations.len()
            //     ))
            //     .unwrap();
            dot_equiv::make_dot(&runner.egraph, &lhs_clone, &rhs_clone)
                .to_svg(format!(
                    "{}/iter_{}.svg",
                    dot_output_dir,
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

    // println!("Egraph pre preconditions: {:#?}", runner.egraph);

    // add the preconditions to the truth values of the egraph
    let truth_id = runner.egraph.add(ModIR::Bool(true));
    for precond in &precond_exprs {
        let p_id = runner.egraph.add_expr(precond);
        runner.egraph.union(truth_id, p_id);
    }

    // println!("Egraph post preconditions: {:#?}", runner.egraph);

    // println!("Expanding the preconditions");
    // let runner = runner.run(&condition_rules());

    let rewrite_rules = &rules();

    let mut runner = runner.run(rewrite_rules);

    let equiv = !runner.egraph.equivs(&lhs_expr, &rhs_expr).is_empty();

    println!(
        "LHS and RHS are{}equivalent!",
        if equiv { " " } else { " not " }
    );

    // let report = runner.report();
    // println!("{report}");

    let id = runner.egraph.find(*runner.roots.first().unwrap());

    if equiv {
        let matches = rhs_pattern.search_eclass(&runner.egraph, id).unwrap();
        let subst = matches.substs[0].clone();
        // don't optimize the length for the first egraph
        runner = runner.without_explanation_length_optimization();
        let mut explained = runner.explain_matches(&lhs_expr, &rhs_pattern.ast, &subst);
        explained.get_string_with_let();
        let flattened = explained.make_flat_explanation().clone();
        let vanilla_len = flattened.len();
        explained.check_proof(rewrite_rules);
        // assert!(explained.get_tree_size() > 0);

        runner = runner.with_explanation_length_optimization();
        let mut explained_short = runner.explain_matches(&lhs_expr, &rhs_pattern.ast, &subst);
        explained_short.get_string_with_let();
        println!("{}", explained_short.get_flat_string());
        let short_len = explained_short.get_flat_strings().len();
        assert!(short_len <= vanilla_len);
        // assert!(explained_short.get_tree_size() > 0);
        explained_short.check_proof(rewrite_rules);
    }
}

fn main() {
    check_equivalence(
        Some("assoc-1"),
        &["(< r q)"],
        "(% r ( + (% p a) (% q (+ (% p b) (% p c)))))",
        "(% r ( + (% q (+ (% p a) (% p b))) (% p c)))",
    );

    check_equivalence(
        Some("assoc-2"),
        &["(< p q)", "(< s q)"],
        "(% r ( + (% p a) (% q (+ (% p b) (% s c)))))",
        "(% r ( + (% q (+ (% p a) (% p b))) (% s c)))",
    );

    check_equivalence(
        Some("assoc-3"),
        &["(< p q)", "(< s q)", "(< r u)"],
        "(% r ( + (% p a) (% u (+ (% p b) (% s c)))))",
        "(% r ( + (% q (+ (% p a) (% p b))) (% s c)))",
    );

    check_equivalence(
        Some("multiply"),
        &["(< p q)", "(> k (+ p p))"],
        "(% r (*
            (% p a)
            (% q (+ (% p b) (% p c)))))",
        "(% r (+
            (% k (* (% p a) (% p b)))
            (% k (* (% p a) (% p c)))))",
    );

    check_equivalence(
        Some("multiply-2"),
        &["(< r q)", "(< r k)"],
        "(% r (*
            (% p a)
            (% q (+ (% p b) (% p c)))))",
        "(% r (+
            (% k (* (% p a) (% p b)))
            (% k (* (% p a) (% p c)))))",
    );

    check_equivalence(
        Some("multiply-3"),
        &["(< r t)", "(< r u)", "(< r v)"],
        "(% r (*
            (% p a)
            (% t (+ (% q b) (% s c)))))",
        "(% r (+
            (% u (* (% p a) (% q b)))
            (% v (* (% p a) (% s c)))))",
    );

    check_equivalence(
        Some("signed"),
        &["sign"],
        "(@ sign (% b a))",
        "(- (* 2 (% (- b 1) a)) (% b a))",
    );

    check_equivalence(Some("test"), &["sign"], "(b)", "(+ 1 (- b 1))");

    check_equivalence(
        Some("signed-1"),
        &["sign"],
        "(@ sign (% b a))",
        "(- (% b (* 2 a)) (% b a))",
    );

    check_equivalence(
        Some("signed-2"),
        &["sign", "(>= p q)"],
        "(% q (@ sign (% p a)))",
        "(% q a)",
    );

    check_equivalence(
        Some("signed-4"),
        &["s"],
        "(+ (@ s (% p a)) (% p a))",
        "(% p (* 2 a))",
    );

    check_equivalence(
        Some("sum"),
        &["(>= p p)"],
        "(% p (+ (% p a) (% p a)))",
        "(% p (* 2 a))",
    );

    // check_equivalence(
    //     Some("signed-2a"),
    //     &["sign", "(> q p)"],
    //     "(% q (@ sign (% p a)))",
    //     "(% q a)",
    // );

    // check_equivalence(
    //     Some("signed-3"),
    //     &["s"],
    //     "(@ s (% q (+ (@ s (% p a)) (@ s (% p b)))))",
    //     //     "(-
    //     //     (% q (+
    //     //         (* 4 (% (- p 1) a))
    //     //             ( + ( ~ (* 2 (% p a))))
    //     //                 (- (* 4 (% (- p 1) b)) (* 2 (% p b))
    //     //         )
    //     //     ))
    //     //     (% q (+ (- (* 2 (% (- p 1) a)) (% p a)) (- (* 2 (% (- p 1) b)) (% p b))))
    //     // )",
    //     "(@ s (% q (+ (- (* 2 (% (- p 1) a)) (% p a)) (- (* 2 (% (- p 1) b)) (% p b)))))",
    // )
    // check_equivalence(
    //     Some("signed-2"),
    //     &["s"],
    //     "(@ s (% q (+ (@ s (% p a)) (@ s (% p b)))))",
    //     "(-
    //         (% q (+
    //             (* 4 (% (- p 1) a))
    //                 ( + ( ~ (* 2 (% p a))))
    //                     (- (* 4 (% (- p 1) b)) (* 2 (% p b))
    //             )
    //         ))
    //         (% q (+ (- (* 2 (% (- p 1) a)) (% p a)) (- (* 2 (% (- p 1) b)) (% p b))))
    //     )",
    //     // "(@ s (% q (+ (- (* 2 (% (- p 1) a)) (% p a)) (- (* 2 (% (- p 1) b)) (% p b)))))",
    // );

    // check_equivalence(
    //     Some("signed"),
    //     &["sign"],
    //     "(@ sign (% p (+ a b)))",
    //     "(@ sign (% p (+ b a)))",
    // );

    // check_equivalence(
    //     Some("signed-assoc"),
    //     &["(< q p)", "s"],
    //     "( + (@ s (% p a)) (@ s (% q (+ (@ s (% p b)) (@ s (% p c))))))",
    //     "( + (@ s (% q (+ (@ s (% p a)) (@ s (% p b))))) (@ s (% p c)))",
    // );
}
