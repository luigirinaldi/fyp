use egg::*;
use num::*;

type Num = num::BigRational;

define_language! {
    enum ModIR {
        "%" = Mod([Id; 2]),      // unary mod operator to capture the bitwidth of a given sub-expression
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

    fn make(egraph: &EGraph<ModIR, Self>, enode: &ModIR) -> Self::Data {
        None
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        DidMerge(false, false)
    }
}

fn insert_some_math_into_an_egraph() {
    // let's try just using the language we just made
    // we'll make an e-graph with just the unit () analysis for now
    let mut egraph = EGraph::<ModIR, ModAnalysis>::default();

    // we can also parse things into RecExprs
    let expr: RecExpr<ModIR> = "(% (+ (% a) (% b)))".parse().unwrap();

    egraph.add_expr(&expr);

    println!("{:#?}", egraph);

    let expr_2: RecExpr<ModIR> = "(% (- (% a) (% c)))".parse().unwrap();

    egraph.add_expr(&expr_2);

    println!("{:#?}", egraph);
}

fn main() {
    println!("Hello, world!");
    insert_some_math_into_an_egraph();
}
