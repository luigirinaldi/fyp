use std::fmt::Debug;
use std::str::FromStr;
use std::time::Duration;

use egg::*;
use num::{BigInt, ToPrimitive};

mod dot_equiv;

use std::fs;
use std::path::Path;
type Num = i32;

define_language! {
    enum ModIR {
        "bw" = Mod([Id; 2]), // mod operator to capture the bitwidth of a given sub-expression
        "@" = Sign([Id; 2]),
        // Arithmetic operators
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "-" = Neg(Id),
        "*" = Mul([Id; 2]),
        // "/" = Div([Id; 2]),
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
            ModIR::Mod([a, b]) => {
                let ax = get(a)?;
                let bx = get(b)?;
                let bexp = 2_i32.pow(bx.clone().to_u32()?);
                Some(((ax % bexp) + bexp) % bexp)
            }
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
            // add a num node
            let id2 = egraph.add(ModIR::Num(n));
            egraph.union(id, id2);
            // // add a mod node (only really works for positive n)
            // let min_width = (n as u32).next_power_of_two().ilog2() + 1;
            // println!("adding {} of bw {}", n, min_width as i32);
            // let bw_id = egraph.add(ModIR::Num(min_width as i32));
            // let id3 = egraph.add(ModIR::Mod([bw_id, id2]));
            // egraph.union(id, id3);
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

        // rewrite!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
        // rewrite!("canon-sub"; "(+ ?a (* -1 ?b))" => "(- ?a ?b)"),
        // rewrite!("cancel-sub"; "(- ?a ?a)" => "0"),

        // rewrite!("minus1-distrib"; "(- ?a ?b)" => "(* -1 (- ?b ?a))"),

        // rewrite!("add2-mul"; "(+ ?a ?a)" => "(* 2 ?a)"),
        rewrite!("mul-add2"; "(* 2 ?a)"  => "(+ ?a ?a)"),

        rewrite!("zero-add"; "(+ ?a 0)" => "?a"),
        // rewrite!("zero-mul"; "(* ?a 0)" => "0"),
        rewrite!("one-mul";  "(* ?a 1)" => "?a"),


        // rewrite!("add-distrib";     "(* ?a (+ ?b ?c))" s=> "(+ (* ?a ?b) (* ?a ?c))"),
        // rewrite!("add-distrib-r";   "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
        // rewrite!("mul-shift"; "(* ?a 2)" => "(<< ?a 1)"),

        // mod related
        // mod sum rewrite where outer bitwidth (p) is lower precision that inner (q)
        rewrite!("mod-sum";
            "(bw ?p (+ (bw ?q ?a) ?b))" => "(bw ?p (+ ?a ?b))"
            if precondition(&["(>= ?q ?p)"])),
        rewrite!("mod-diff";
            "(bw ?p (- (bw ?q ?a) ?b))" => "(bw ?p (- ?a ?b))"
            if precondition(&["(>= ?q ?p)"])),
        rewrite!("mod-diff-2";
            "(bw ?p (- ?a (bw ?q ?b)))" => "(bw ?p (- ?a ?b))"
            if precondition(&["(>= ?q ?p)"])),
        // mod sum rewrite preserving full precision
        rewrite!("mod-sum-1";
            "(bw ?p (+ (bw ?q ?a) (bw ?r ?b)))" => "(+ (bw ?q ?a) (bw ?r ?b))"
            if precondition(&["(< ?q ?p)","(< ?r ?p)"])),
        // precision preserving transform
        rewrite!("mod-mul-simp1";
            "(bw ?r (* (bw ?q ?a) (bw ?p ?b)))" => "(* (bw ?q ?a) (bw ?p ?b))"
            if precondition(&["(>= ?r (+ ?p ?q))"])),
        // precision loss due to smaller outer mod
        rewrite!("mod-mul-simp2";
            "(bw ?q (* (bw ?p ?a) ?b))" => "(bw ?q (* ?a ?b))"
            if precondition(&["(>= ?p ?q)"])),

        rewrite!("mod-reduce-1"; "(bw ?q (bw ?p ?a))" => "(bw ?p a)" if precondition(&["(>= ?q ?p)"])),
        // rewrite!("mod-reduce-2"; "(bw ?q (bw ?p ?a))" => "(bw ?q a)" if precondition(&["(< ?q ?p)"])),

        // sign related
        // rewrite!("signed";
        //     "(@ ?s (bw ?bw ?a))" => "(- (* 2 (bw (- ?bw 1) ?a)) (bw ?bw ?a))"
        //     if precondition(&["(?s)"])
        // )
    ];
    rules.extend(rewrite!("add-distrib"; "(* ?a (+ ?b ?c))" <=> "(+ (* ?a ?b) (* ?a ?c))"));
    rules.extend(rewrite!("sub-add"; "(- ?a ?b)" <=> "(+ ?a (- ?b))"));
    // rules.extend(rewrite!("sub-neg"; "(- ?b)" <=> "(* -1 ?b)"));
    // multliplication across the mod (this works because mod b implies mod 2^b)
    // rules.extend(rewrite!("mod-mul"; "(* 2 (bw ?b ?c))" <=> "(bw (+ 1 ?b) (* 2 ?c))"));
    rules.extend(rewrite!("gt-lt"; "(> ?a ?b)" <=> "(< ?b ?a)"));
    rules.extend(rewrite!("gte-lte"; "(>= ?a ?b)" <=> "(<= ?b ?a)"));
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
        // .with_iter_limit(50)
        .with_time_limit(Duration::from_secs(20))
        .with_hook(move |runner| {
            dot_equiv::make_dot(&runner.egraph, &lhs_clone, &rhs_clone)
                .to_pdf(format!(
                    "{}/iter_{}.pdf",
                    dot_output_dir,
                    runner.iterations.len()
                ))
                .unwrap();
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

    // add the preconditions to the truth values of the egraph
    let truth_id = runner.egraph.add(ModIR::Bool(true));
    for precond in &precond_exprs {
        let p_id = runner.egraph.add_expr(precond);
        runner.egraph.union(truth_id, p_id);
    }

    let rewrite_rules = &rules();

    let mut runner = runner.run(rewrite_rules);

    let equiv = !runner.egraph.equivs(&lhs_expr, &rhs_expr).is_empty();

    println!(
        "{} LHS and RHS are{}equivalent!",
        name,
        if equiv { " " } else { " not " }
    );

    let id = runner.egraph.find(*runner.roots.first().unwrap());

    if equiv {
        let matches = rhs_pattern.search_eclass(&runner.egraph, id).unwrap();
        let subst = matches.substs[0].clone();

        runner = runner.with_explanation_length_optimization();
        let mut explained_short = runner.explain_matches(&lhs_expr, &rhs_pattern.ast, &subst);
        explained_short.get_string_with_let();
        for s in explained_short.get_flat_strings() {
            println!("    {:#}", s);
        }
        explained_short.check_proof(rewrite_rules);
    }
}

fn main() {
    // check_equivalence(
    //     Some("mult_sum_same_nomod"),
    //     &[],
    //     "(+ (* a b) b)",
    //     "(* (+ a 1) b)",
    // );

    // check_equivalence(
    //     Some("mult_sum_same"),
    //     &["(> t p)", "(> t 1)", "(>= s (+ p q))"],
    //     "(bw r (+ (bw s (* (bw p a) (bw q b))) (bw q b)))",
    //     "(bw r (* (bw t (+ (bw p a) (bw 1 1))) (bw q b)))",
    // );

    check_equivalence(
        Some("commutativity-add"),
        &[],
        "(bw r ( + (bw p a) (bw q b)))",
        "(bw r ( + (bw q b) (bw p a)))",
    );

    check_equivalence(
        Some("commutativity-mult"),
        &[],
        "(bw r ( * (bw p a) (bw q b)))",
        "(bw r ( * (bw q b) (bw p a)))",
    );

    check_equivalence(
        Some("mult-assoc-1"),
        &["(>= q t)", "(>= u t)"],
        "(bw t ( * (bw u (* (bw p a) (bw r b))) (bw s c)))",
        "(bw t ( * (bw p a) (bw q (* (bw r b) (bw s c)))))",
    );

    check_equivalence(
        Some("mult-assoc-2"),
        &["(>= q t)", "(<= (+ p r) u)"],
        "(bw t ( * (bw u (* (bw p a) (bw r b))) (bw s c)))",
        "(bw t ( * (bw p a) (bw q (* (bw r b) (bw s c)))))",
    );

    check_equivalence(
        Some("mult-assoc-3"),
        &["(<= (+ r s) q)", "(>= u t)"],
        "(bw t ( * (bw u (* (bw p a) (bw r b))) (bw s c)))",
        "(bw t ( * (bw p a) (bw q (* (bw r b) (bw s c)))))",
    );

    check_equivalence(
        Some("mult-assoc-4"),
        &["(<= (+ r s) q)", "(<= (+ p r) u)"],
        "(bw t ( * (bw u (* (bw p a) (bw r b))) (bw s c)))",
        "(bw t ( * (bw p a) (bw q (* (bw r b) (bw s c)))))",
    );

    check_equivalence(
        Some("add-assoc-1"),
        &["(>= q t)", "(>= u t)"],
        "(bw t ( + (bw u (+ (bw p a) (bw r b))) (bw s c)))",
        "(bw t ( + (bw p a) (bw q (+ (bw r b) (bw s c)))))",
    );

    check_equivalence(
        Some("add-assoc-2"),
        &["(< r q)", "(< s q)", "(>= u t)"],
        "(bw t ( + (bw u (+ (bw p a) (bw r b))) (bw s c)))",
        "(bw t ( + (bw p a) (bw q (+ (bw r b) (bw s c)))))",
    );

    check_equivalence(
        Some("add-assoc-3"),
        &["(>= q t)", "(< p u)", "(< r u)"],
        "(bw t ( + (bw u (+ (bw p a) (bw r b))) (bw s c)))",
        "(bw t ( + (bw p a) (bw q (+ (bw r b) (bw s c)))))",
    );

    check_equivalence(
        Some("add-assoc-4"),
        &["(< r q)", "(< s q)", "(< p u)", "(< r u)"],
        "(bw t ( + (bw u (+ (bw p a) (bw r b))) (bw s c)))",
        "(bw t ( + (bw p a) (bw q (+ (bw r b) (bw s c)))))",
    );

    check_equivalence(
        Some("dist-over-add"),
        &["(>= q r)", "(>= u r)", "(>= v r)"],
        "(bw r (* (bw p a) (+ (bw s b) (bw t c))))",
        "(bw r (+ (bw u (* (bw p a) (bw s b))) (bw v (* (bw p a) (bw t c)) ) ))",
    );

    check_equivalence(
        Some("sum-same"),
        &[],
        "(bw q (+ (bw p a) (bw p a)))",
        "(bw q (* (bw 2 2) (bw p a)))",
    );

    check_equivalence(
        Some("mult_sum_same"),
        &["(> t p)", "(> t 1)", "(>= s (+ p q))"],
        "(bw r (+ (bw s (* (bw p a) (bw q b))) (bw q b)))",
        "(bw r (* (bw t (+ (bw p a) (bw 1 1))) (bw q b)))",
    );

    check_equivalence(
        Some("add_zero"),
        &["(>= p p)"],
        "(bw p (+ (bw p a) 0))",
        "(bw p a)",
    );

    check_equivalence(
        Some("sub_to_neg"),
        &[],
        "(bw r (- (bw p a) (bw q b)))",
        "(bw r (+ (bw p a) (- (bw q b))))",
    );

    check_equivalence(
        Some("mul_one"),
        &["(>= p p)"],
        "(bw p (* (bw p a) 1))",
        "(bw p a)",
    );

    check_equivalence(
        Some("add-assoc-paper"),
        &["(>= q r)"],
        "(bw r ( + (bw q (+ (bw p a) (bw p b))) (bw p c)))",
        "(bw r ( + (bw p a) (bw q (+ (bw p b) (bw p c)))))",
    );

    // check_equivalence(
    //     Some("assoc-2"),
    //     &["(< p q)", "(< s q)"],
    //     "(bw r ( + (bw p a) (bw q (+ (bw p b) (bw s c)))))",
    //     "(bw r ( + (bw q (+ (bw p a) (bw p b))) (bw s c)))",
    // );

    // check_equivalence(
    //     Some("assoc-3"),
    //     &["(< p q)", "(< s q)", "(< r u)"],
    //     "(bw r ( + (bw p a) (bw u (+ (bw p b) (bw s c)))))",
    //     "(bw r ( + (bw q (+ (bw p a) (bw p b))) (bw s c)))",
    // );

    // check_equivalence(
    //     Some("multiply"),
    //     &["(< p q)", "(> k (+ p p))"],
    //     "(bw r (*
    //         (bw p a)
    //         (bw q (+ (bw p b) (bw p c)))))",
    //     "(bw r (+
    //         (bw k (* (bw p a) (bw p b)))
    //         (bw k (* (bw p a) (bw p c)))))",
    // );

    // check_equivalence(
    //     Some("multiply-2"),
    //     &["(< r q)", "(< r k)"],
    //     "(bw r (*
    //         (bw p a)
    //         (bw q (+ (bw p b) (bw p c)))))",
    //     "(bw r (+
    //         (bw k (* (bw p a) (bw p b)))
    //         (bw k (* (bw p a) (bw p c)))))",
    // );

    // check_equivalence(
    //     Some("multiply-3"),
    //     &["(< r t)", "(< r u)", "(< r v)"],
    //     "(bw r (*
    //         (bw p a)
    //         (bw t (+ (bw q b) (bw s c)))))",
    //     "(bw r (+
    //         (bw u (* (bw p a) (bw q b)))
    //         (bw v (* (bw p a) (bw s c)))))",
    // );

    // check_equivalence(
    //     Some("signed"),
    //     &["sign"],
    //     "(@ sign (bw b a))",
    //     "(- (* 2 (bw (- b 1) a)) (bw b a))",
    // );

    // check_equivalence(Some("test"), &["sign"], "(b)", "(+ 1 (- b 1))");

    // check_equivalence(
    //     Some("signed-1"),
    //     &["sign"],
    //     "(@ sign (bw b a))",
    //     "(- (bw b (* 2 a)) (bw b a))",
    // );

    // check_equivalence(
    //     Some("signed-2"),
    //     &["sign", "(>= p q)"],
    //     "(bw q (@ sign (bw p a)))",
    //     "(bw q a)",
    // );

    // // check_equivalence(
    // //     Some("signed-2a"),
    // //     &["sign", "(> q p)"],
    // //     "(bw q (@ sign (bw p a)))",
    // //     "(bw q a)",
    // // );

    // check_equivalence(
    //     Some("signed-4"),
    //     &["s"],
    //     "(+ (@ s (bw p a)) (bw p a))",
    //     "(bw p (* 2 a))",
    // );

    // check_equivalence(
    //     Some("sum"),
    //     &["(>= p q)"],
    //     "(bw q (+ (bw p a) (bw p a)))",
    //     "(bw q (* 2 a))",
    // );

    // // check_equivalence(
    // //     Some("signed-3"),
    // //     &["s"],
    // //     "(@ s (bw q (+ (@ s (bw p a)) (@ s (bw p b)))))",
    // //     //     "(-
    // //     //     (bw q (+
    // //     //         (* 4 (bw (- p 1) a))
    // //     //             ( + ( ~ (* 2 (bw p a))))
    // //     //                 (- (* 4 (bw (- p 1) b)) (* 2 (bw p b))
    // //     //         )
    // //     //     ))
    // //     //     (bw q (+ (- (* 2 (bw (- p 1) a)) (bw p a)) (- (* 2 (bw (- p 1) b)) (bw p b))))
    // //     // )",
    // //     "(@ s (bw q (+ (- (* 2 (bw (- p 1) a)) (bw p a)) (- (* 2 (bw (- p 1) b)) (bw p b)))))",
    // // )
    // // check_equivalence(
    // //     Some("signed-3"),
    // //     &["s"],
    // //     "(@ s (bw q (+ (@ s (bw p a)) (@ s (bw p b)))))",
    // //     "(-
    // //         (bw q (+
    // //             (* 4 (bw (- p 1) a))
    // //                 ( + ( ~ (* 2 (bw p a))))
    // //                     (- (* 4 (bw (- p 1) b)) (* 2 (bw p b))
    // //             )
    // //         ))
    // //         (bw q (+ (- (* 2 (bw (- p 1) a)) (bw p a)) (- (* 2 (bw (- p 1) b)) (bw p b))))
    // //     )",
    // //     // "(@ s (bw q (+ (- (* 2 (bw (- p 1) a)) (bw p a)) (- (* 2 (bw (- p 1) b)) (bw p b)))))",
    // // );

    // // check_equivalence(
    // //     Some("signed"),
    // //     &["sign"],
    // //     "(@ sign (bw p (+ a b)))",
    // //     "(@ sign (bw p (+ b a)))",
    // // );

    // // check_equivalence(
    // //     Some("signed-assoc"),
    // //     &["(< q (+ p 1))", "s"],
    // //     "(bw r ( + (@ s (bw p a)) (@ s (bw q (+ (@ s (bw p b)) (@ s (bw p c)))))))",
    // //     "(bw r ( + (@ s (bw p a)) (+ (bw q (+ (* 2 b) (* 2 c))) (bw q (+ b c)))))", // "(bw r ( + (@ s (bw q (+ (@ s (bw p a)) (@ s (bw p b))))) (@ s (bw p c))))",
    // // );
}
