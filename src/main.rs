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
        // Numbers
        Num(Num),
        // variables on which the operators operate
        Var(Symbol),
    }
}

// Analysis for this framework, doesn't actually do anything except hold the
// name of the identifier for the mod operator
#[derive(Default)]
struct ModAnalysis;

impl Analysis<ModIR> for ModAnalysis {
    type Data = Option<String>;

    fn make(_egraph: &EGraph<ModIR, Self>, _enode: &ModIR) -> Self::Data {
        None
    }

    fn merge(&mut self, _a: &mut Self::Data, _b: Self::Data) -> DidMerge {
        DidMerge(false, false)
    }
}

#[rustfmt::skip]
fn rules() -> Vec<Rewrite<ModIR, ModAnalysis>> {
    vec![
        rewrite!("comm-add";    "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("mod-sum";     "(% ?p (+ (% ?q ?a) ?b))" => "(% ?p (+ ?a ?b))")
    ]
}

fn make_assoc_expr() {
    // let's try just using the language we just made
    // we'll make an e-graph with just the unit () analysis for now
    let mut egraph = EGraph::<ModIR, ModAnalysis>::default();

    let expr_a: RecExpr<ModIR> = "(% p (+ a b))".parse().unwrap();
    let _var_a = egraph.add_expr(&expr_a);
    // let expr_b: RecExpr<ModIR> = "(% b)".parse().unwrap();
    // let var_b = egraph.add_expr(&expr_b);
    // let expr_c: RecExpr<ModIR> = "(% c)".parse().unwrap();
    // let var_c = egraph.add_expr(&expr_c);

    // egraph.set_analysis_data(var_a, Some(String::from("p")));
    // egraph.set_analysis_data(var_b, Some(String::from("p")));
    // egraph.set_analysis_data(var_c, Some(String::from("p")));

    println!("{:#?}", egraph);
}

fn check_equivalence(start: &str, end: &str) {
    let rewrite_rules = &rules();

    let start_expr: RecExpr<ModIR> = start.parse().unwrap();
    let goals: &[Pattern<ModIR>] = &[end.parse().unwrap()];
    let mut runner = Runner::default()
        .with_explanations_enabled()
        // .without_explanation_length_optimization()
    ;

    runner = runner.with_expr(&start_expr);
    // NOTE this is a bit of hack, we rely on the fact that the
    // initial root is the last expr added by the runner. We can't
    // use egraph.find_expr(start) because it may have been pruned
    // away
    let id = runner.egraph.find(*runner.roots.last().unwrap());

    let goals_vec = goals.to_vec();
    runner = runner.with_hook(move |r| {
        if goals_vec
            .iter()
            .all(|g: &Pattern<_>| g.search_eclass(&r.egraph, id).is_some())
        {
            Err("Proved all goals".into())
        } else {
            Ok(())
        }
    });
    let mut runner = runner.run(rewrite_rules);

    let report = runner.report();
    println!("{report}");
    runner.egraph.check_goals(id, goals);

    if runner.egraph.are_explanations_enabled() {
        for goal in goals {
            let matches = goal.search_eclass(&runner.egraph, id).unwrap();
            let subst = matches.substs[0].clone();
            // don't optimize the length for the first egraph
            runner = runner.without_explanation_length_optimization();
            let mut explained = runner.explain_matches(&start_expr, &goal.ast, &subst);
            explained.get_string_with_let();
            let flattened = explained.make_flat_explanation().clone();
            let vanilla_len = flattened.len();
            explained.check_proof(rewrite_rules);
            assert!(explained.get_tree_size() > 0);

            runner = runner.with_explanation_length_optimization();
            let mut explained_short = runner.explain_matches(&start_expr, &goal.ast, &subst);
            explained_short.get_string_with_let();
            println!("{}", explained_short.get_flat_string());
            let short_len = explained_short.get_flat_strings().len();
            assert!(short_len <= vanilla_len);
            assert!(explained_short.get_tree_size() > 0);
            explained_short.check_proof(rewrite_rules);
        }
    }
}

fn main() {
    println!("Hello, world!");
    // make_assoc_expr();
    //

    // egg::test::test_runner(
    //     "Simple test",
    //     None,
    //     &rules(),
    //     "(% r ( + (% p a) (% q (+ (% p b) (% p c)))))"
    //         .parse()
    //         .unwrap(),
    //     &["(% r ( + (% p a) (+ (% p b) (% p c))))".parse().unwrap()],
    //     None,
    //     true,
    // );
    //
    check_equivalence(
        "(% r ( + (% p a) (% q (+ (% p b) (% p c)))))",
        "(% r ( + (% p a) (+ (% p b) (% p c))))",
    );

    check_equivalence("(+ a (+ b (+ c d)))", "(+ (+ (+ c d) b) a)");

    // egg::test::test_runner(
    //     "Simple test",
    //     Some(Runner::default().with_explanations_enabled()),
    //     &rules(),
    //     "(+ a (+ a b))".parse().unwrap(),
    //     &["(+ (+ b a) a)".parse().unwrap()],
    //     None,
    //     true,
    // );

    // egg::test_fn! {
    //     simple_test, rules(),
    //     "% r ( + (% p a) (% q (+ (% p b) (% p c))))"
    //     =>
    //     "% r ( + (% p a) (+ (% p b) (% p c)))"
    // }
}
