use egg::*;

type Num = num::BigRational;

define_language! {
    enum ModIR {
        "%" = Mod([Id; 2]),      // mod operator to capture the bitwidth of a given sub-expression
        // Arithmetic operators
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        // Operators to handle preconditions
        ">"  = GT([Id; 2]),
        ">=" = GTE([Id; 2]),
        "<"  = LT([Id; 2]),
        "<=" = LTE([Id; 2]),
        // Numbers
        Num(Num),
        // variables on which the operators operate
        Var(Symbol),
        Bool(bool),
    }
}

// Analysis for this framework, doesn't actually do anything except hold the
// name of the identifier for the mod operator
#[derive(Default)]
struct ModAnalysis;

impl Analysis<ModIR> for ModAnalysis {
    type Data = Option<Vec<String>>;

    fn make(_egraph: &EGraph<ModIR, Self>, enode: &ModIR) -> Self::Data {
        match enode {
            _ => None,
        }
    }

    fn merge(&mut self, _a: &mut Self::Data, _b: Self::Data) -> DidMerge {
        DidMerge(false, false)
    }
}

#[rustfmt::skip]
fn rules() -> Vec<Rewrite<ModIR, ModAnalysis>> {
    vec![
        // normal arithmetic
        rewrite!("add-comm";    "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("add-assoc";   "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),

        // mod related
        rewrite!("mod-sum";     "(% ?p (+ (% ?q ?a) ?b))"           => "(% ?p (+ ?a ?b))" if less_than("?p", "?q")),         // if q >= p
        rewrite!("mod-sum-1";   "(% ?p (+ (% ?q ?a) (% ?q ?b)))"    => "(+ (% ?q ?a) (% ?q ?b))" if less_than("?q","?p")),  // if q  < p

    ]
}

// fn check_condition(cond: &str) -> impl Fn(&mut EGraph<ModIR, ModAnalysis>, Id, &Subst) -> bool {
//     let cond_expr: RecExpr<ModIR> = cond.parse().unwrap();
//     println!("printing conditions {:#?}", cond_expr);
//     // look up the expr in the egraph
//     // if a vector of ids is returned then check that they are in the same eclass as the truth node
//     move |egraph, _root, _subst| {
//         egraph
//             .lookup_expr_ids(&cond_expr)
//             .and_then(|ids| {
//                 egraph
//                     .lookup(ModIR::Bool(true))
//                     .and_then(|truth| Some(ids.iter().any(|&id| id == truth)))
//             })
//             .unwrap_or(false)
//     }
// }

// implements a < b
fn less_than(a: &str, b: &str) -> impl Fn(&mut EGraph<ModIR, ModAnalysis>, Id, &Subst) -> bool {
    let a_var: Var = a.parse().unwrap();
    let b_var: Var = b.parse().unwrap();
    move |egraph, _root, subst: &Subst| {
        let res = egraph
            .lookup(ModIR::LT([subst[a_var], subst[b_var]]))
            .and_then(|comp_id| {
                egraph
                    .lookup(ModIR::Bool(true))
                    .and_then(|truth| Some(truth == comp_id))
            })
            .unwrap_or(false);
        println!(
            "Entering conditional {} < {} = {}",
            egraph.id_to_expr(subst[a_var]),
            egraph.id_to_expr(subst[b_var]),
            res
        );
        res
    }
}

// preconditions encoded as a list of conjunctions
fn check_equivalence(preconditions: &[&str], lhs: &str, rhs: &str) {
    let rewrite_rules = &rules();

    let precond_exprs: Vec<RecExpr<ModIR>> =
        preconditions.iter().map(|&p| p.parse().unwrap()).collect();

    let lhs_expr: RecExpr<ModIR> = lhs.parse().unwrap();
    let rhs_expr: RecExpr<ModIR> = rhs.parse().unwrap();
    let lhs_pattern = Pattern::from(&lhs_expr);
    let rhs_pattern = Pattern::from(&rhs_expr);
    let mut runner = Runner::default()
        .with_explanations_enabled()
        // .without_explanation_length_optimization()
        .with_expr(&lhs_expr)
        .with_expr(&rhs_expr);

    // println!("Egraph pre preconditions: {:#?}", runner.egraph);

    // add the preconditions to the truth values of the egraph
    let truth_id = runner.egraph.add(ModIR::Bool(true));
    for precond in &precond_exprs {
        println!("{:?}", precond);
        let p_id = runner.egraph.add_expr(precond);
        runner.egraph.union(truth_id, p_id);
    }

    // println!("Egraph post preconditions: {:#?}", runner.egraph);

    let mut runner = runner.run(rewrite_rules);

    let equiv = !runner.egraph.equivs(&lhs_expr, &rhs_expr).is_empty();

    println!(
        "LHS and RHS are{}equivalent!",
        if equiv { " " } else { " not " }
    );

    let report = runner.report();
    println!("{report}");

    let id = runner.egraph.find(*runner.roots.first().unwrap());

    if runner.egraph.are_explanations_enabled() {
        let matches = rhs_pattern.search_eclass(&runner.egraph, id).unwrap();
        let subst = matches.substs[0].clone();
        // don't optimize the length for the first egraph
        runner = runner.without_explanation_length_optimization();
        let mut explained = runner.explain_matches(&lhs_expr, &rhs_pattern.ast, &subst);
        explained.get_string_with_let();
        let flattened = explained.make_flat_explanation().clone();
        let vanilla_len = flattened.len();
        explained.check_proof(rewrite_rules);
        assert!(explained.get_tree_size() > 0);

        runner = runner.with_explanation_length_optimization();
        let mut explained_short = runner.explain_matches(&lhs_expr, &rhs_pattern.ast, &subst);
        explained_short.get_string_with_let();
        println!("{}", explained_short.get_flat_string());
        let short_len = explained_short.get_flat_strings().len();
        assert!(short_len <= vanilla_len);
        assert!(explained_short.get_tree_size() > 0);
        explained_short.check_proof(rewrite_rules);
    }
}

fn main() {
    println!("Hello, world!");

    check_equivalence(
        &["(< r q)"],
        "(% r ( + (% p a) (% q (+ (% p b) (% p c)))))",
        "(% r ( + (% q (+ (% p a) (% p b))) (% p c)))",
    );
}
