use crate::Symbol;
use egg::*;
use num::PrimInt;
use std::fs::File;
use std::io::{Error, Write};
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

#[rustfmt::skip]
fn rules() -> Vec<Rewrite<ModIR, ModAnalysis>> {
    let mut rules = vec![
        // normal arithmetic
        rewrite!("add.commute";    "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("add.assoc";   "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rewrite!("mul-comm";    "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("mul-assoc";   "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),
        rewrite!("pow_sum";     "(* (^ ?a ?b) (^ ?a ?c))" => "(^ ?a (+ ?b ?c))"),
        rewrite!("div-add";     "(÷ (+ ?a ?b) ?c)" => "(+ (÷ ?a ?c) (÷ ?b ?c))"),
        rewrite!("div-mul";     "(÷ (* ?a ?b) ?c)" => "(* (÷ ?a ?c) ?b)"),
        rewrite!("div-mul2";    "(÷ (÷ ?a ?b) ?c)" => "(÷ ?a (* ?b ?c))"),

        // rewrite!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
        // rewrite!("canon-sub"; "(+ ?a (* -1 ?b))" => "(- ?a ?b)"),
        rewrite!("cancel-sub"; "(- ?a ?a)" => "0"),

        // rewrite!("minus1-distrib"; "(- ?a ?b)" => "(* -1 (- ?b ?a))"),

        // identities
        rewrite!("add2-mul"; "(+ ?a ?a)" => "(* 2 ?a)"),
        rewrite!("mul-add2"; "(* 2 ?a)"  => "(+ ?a ?a)"),
        rewrite!("zero-add"; "(+ ?a 0)" => "?a"),
        rewrite!("zero-mul"; "(* ?a 0)" => "0"),
        rewrite!("one-mul";  "(* ?a 1)" => "?a"),
        rewrite!("div-same"; "(÷ ?a ?a)" => "1"),

        // mod related
        // mod sum rewrite where outer bitwidth (p) is lower precision that inner (q)
        rewrite!("mod-1"; "(bw ?p 1)" => "1"),
        rewrite!("mod-0"; "(bw ?p 0)" => "0"),
        rewrite!("add_remove_prec";
            "(bw ?p (+ (bw ?q ?a) ?b))" => "(bw ?p (+ ?a ?b))"
            if precondition(&["(>= ?q ?p)"])),
        // rewrite!("mod-diff";
        //     "(bw ?p (- (bw ?q ?a) ?b))" => "(bw ?p (- ?a ?b))"
        //     if precondition(&["(>= ?q ?p)"])),
        // rewrite!("mod-diff-2";
        //     "(bw ?p (- ?a (bw ?q ?b)))" => "(bw ?p (- ?a ?b))"
        //     if precondition(&["(>= ?q ?p)"])),
        // mod sum rewrite preserving full precision
        rewrite!("add_full_prec";
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
        rewrite!("div-simp"; "(bw ?p (÷ (bw ?q ?a) ?b))" => "(÷ (bw ?q ?a) ?b)" if precondition(&["(>= ?p ?q)"])),

        rewrite!("mod-reduce-1"; "(bw ?q (bw ?p ?a))" => "(bw ?p a)" if precondition(&["(>= ?q ?p)"])),
        // rewrite!("mod-reduce-2"; "(bw ?q (bw ?p ?a))" => "(bw ?q a)" if precondition(&["(< ?q ?p)"])),

        // rewrite!("pow-bw"; "(^ 2 (bw ?p ?a))" => "(bw (- (^ 2 ?p) 1) (^ 2 (bw ?p ?a))))"),
        rewrite!("mul-pow2"; "(bw ?s (* (bw ?p ?a) (^ 2 (bw ?q ?b))))" => "(* (bw ?p ?a) (^ 2 (bw ?q ?b)))" if precondition(&["(>= ?s (+ ?p (- (^ 2 ?q) 1)))"])),
        // rewrite!("pow-bw"; "(^ 2 (bw ?p ?a))" => "(bw (^ 2 ?p) (^ 2 (bw ?p ?a))))"),

        // sign related
        rewrite!("signed";
            "(@ ?s (bw ?bw ?a))" => "(- (* 2 (bw (- ?bw 1) ?a)) (bw ?bw ?a))"
            if precondition(&["(?s)"])
        ),

        // shift operations
        rewrite!("left-shift"; "(<< ?a ?b)" => "(* ?a (^ 2 ?b))"),
        rewrite!("right-shift"; "(>> ?a ?b)" => "(÷ ?a (^ 2 ?b))"),
        // multi_rewrite!("trans"; "?p = (> ?a ?b) = true, ?q = (> b c) = true" => "?r = (> a c) = true")
    ];
    rules.extend(rewrite!("add-distrib"; "(* ?a (+ ?b ?c))" <=> "(+ (* ?a ?b) (* ?a ?c))"));
    rules.extend(rewrite!("sub-add"; "(- ?a ?b)" <=> "(+ ?a (- ?b))"));
    // rules.extend(rewrite!("sub-neg"; "(- ?b)" <=> "(* -1 ?b)"));
    // multliplication across the mod (this works because mod b implies mod 2^b)
    // c * (a mod b) = (c * a mod b * c)
    // rules.extend(rewrite!("mod-mul"; "(* (^ 2 ?e) (bw ?b ?c))" <=> "(bw (+ ?e ?b) (* (^ 2 ?e) ?c))"));
    rules.extend(rewrite!("gt-lt"; "(> ?a ?b)" <=> "(< ?b ?a)"));
    rules.extend(rewrite!("gte-lte"; "(>= ?a ?b)" <=> "(<= ?b ?a)"));
    // rules.extend();
    rules
}

fn recursive_node_clone(
    egraph: &EGraph<ModIR, ModAnalysis>,
    root_id: &Id,
    new_expr: &mut RecExpr<ModIR>,
) -> Id {
    let root_node = egraph.id_to_node(*root_id);
    match root_node {
        ModIR::Var(s) => new_expr.add(ModIR::Var(*s)),
        ModIR::Mod([a, b]) => {
            let id_a = recursive_node_clone(egraph, a, new_expr);
            let id_b = recursive_node_clone(egraph, b, new_expr);

            new_expr.add(ModIR::Mod([id_a, id_b]))
        }
        ModIR::Div([a, b]) => {
            let id_a = recursive_node_clone(egraph, a, new_expr);
            let id_b = recursive_node_clone(egraph, b, new_expr);

            new_expr.add(ModIR::Div([id_a, id_b]))
        }
        ModIR::Pow([a, b]) => {
            let id_a = recursive_node_clone(egraph, a, new_expr);
            let id_b = recursive_node_clone(egraph, b, new_expr);

            new_expr.add(ModIR::Pow([id_a, id_b]))
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
            recursive_node_clone(egraph, subst.get(var).unwrap(), new_expr)
        }
        ModIR::Div([a, b]) => {
            let id_a = apply_subst(egraph, subst, base_expr, a, new_expr);
            let id_b = apply_subst(egraph, subst, base_expr, b, new_expr);
            new_expr.add(ModIR::Div([id_a, id_b]))
        }
        ModIR::Pow([a, b]) => {
            let id_a = apply_subst(egraph, subst, base_expr, a, new_expr);
            let id_b = apply_subst(egraph, subst, base_expr, b, new_expr);
            new_expr.add(ModIR::Pow([id_a, id_b]))
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
// TODO reimplement this using multipatterns https://github.com/luigirinaldi/fyp/issues/1
fn precondition(conds: &[&str]) -> impl Fn(&mut EGraph<ModIR, ModAnalysis>, Id, &Subst) -> bool {
    let cond_exprs: Vec<RecExpr<ModIR>> = conds.iter().map(|expr| expr.parse().unwrap()).collect();
    // look up the expr in the egraph then check that they are in the same eclass as the truth node
    move |egraph, _root, subst| {
        let mut res = true;
        let mut log = String::default();
        for expr in &cond_exprs {
            let mut cond_subst: RecExpr<ModIR> = RecExpr::default();

            apply_subst(egraph, subst, expr, expr.root(), &mut cond_subst);

            // println!(
            //     "{:#?} => {:#?}",
            //     expr.to_string(),
            //     cond_subst.to_string(),
            //     // cond_subst
            // );
            res &= egraph
                .lookup_expr_ids(&cond_subst)
                .and_then(|ids| {
                    egraph
                        .lookup(ModIR::Bool(true))
                        .and_then(|truth| Some(ids.iter().any(|&id| id == truth)))
                })
                .unwrap_or(false);
            log.push_str(
                format!(
                    "{} => {}: {}\n&",
                    expr.to_string(),
                    cond_subst.to_string(),
                    res
                )
                .as_str(),
            );
        }
        // print!("{}", log);
        res
    }
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

// preconditions encoded as a list of conjunctions
pub fn check_equivalence(
    name_str: Option<&str>,
    preconditions: &[&str],
    lhs: &str,
    rhs: &str,
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
        runner.egraph.union(truth_id, p_id);
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
            "{}\nlhs:{}\nrhs:{}\nconditions:{:?}\n\n",
            output_str,
            lhs_expr.to_string(),
            rhs_expr.to_string(),
            preconditions
        )
        .as_bytes(),
    )?;
    print!("{}", output_str);

    let id = runner.egraph.find(*runner.roots.first().unwrap());

    if equiv {
        let matches = rhs_pattern.search_eclass(&runner.egraph, id).unwrap();
        let subst = matches.substs[0].clone();

        runner = runner.with_explanation_length_optimization();
        let mut explained_short = runner.explain_matches(&lhs_expr, &rhs_pattern.ast, &subst);
        explained_short.check_proof(rewrite_rules);

        let mut flat_terms = explained_short.make_flat_explanation().iter();
        // sanitize the name of the test to remove chars isabelle doesn't like
        let proof_name = name.replace("/", "_").replace(".rs", "");
        let proof_file_path = output_dir.clone() + &format!("/{}.thy", proof_name);
        let mut proof_file = File::create(proof_file_path)?;

        proof_file.write(
            format!(
                "theory {th_name}
    imports rewrite_lemmas
begin
theorem {th_name}_th:
\"{lhs}={rhs}\" (is \"?lhs = ?rhs\")
if {preconditions}
proof -\n",
                th_name = proof_name,
                lhs = lhs_expr.to_string(),
                rhs = rhs_expr.to_string(),
                preconditions = preconditions
                    .iter()
                    .map(|p| format!("\"{}\"", p))
                    .collect::<Vec<_>>()
                    .join(" and "),
            )
            .as_bytes(),
        )?;

        let mut prev_term = flat_terms.next().unwrap().remove_rewrites();
        for (i, term) in flat_terms.enumerate() {
            // println!(
            //     "{} {:#?} {:#?} {} {:#?}",
            //     i,
            //     // term.to_string(),
            //     term.remove_rewrites().to_string(),
            //     term.has_rewrite_forward(),
            //     term.has_rewrite_backward(),
            //     term.get_rewrite(),
            // );
            println!("{:#?}", term);

            let (bw, fw) = term.get_rewrite();
            let rw = if bw.is_some() {
                bw.unwrap()
            } else {
                fw.unwrap()
            };
            // assuming if one isn't defined the other one is
            let rw_dir = fw.is_some();
            println!(
                "{}: {} {} {} using {}",
                i,
                prev_term.to_string(),
                if rw_dir { "->" } else { "<-" },
                term.remove_rewrites().to_string(),
                rw
            );
            proof_file.write(
                format!(
                    "   {prefix}have \"{lhs} = {term}\" using that by (simp only: {rw_rule})\n",
                    prefix = if i == 0 { "" } else { "moreover " },
                    lhs = if i == 0 { "?lhs" } else { "..." },
                    term = term.remove_rewrites().to_string(),
                    rw_rule = rw.to_string()
                )
                .as_bytes(),
            )?;
            prev_term = term.remove_rewrites();
        }

        proof_file.write("ultimately show ?thesis by argo\nqed\nend".as_bytes())?;

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

        Ok(())
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
