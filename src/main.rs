use egg::*;
use std::slice::{from_mut, from_ref};

type Num = num::BigRational;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ModIR {
    Mod(String, Id),
    Add([Id; 2]),
    Sub([Id; 2]),
    Mul([Id; 2]),
    Div([Id; 2]),
    Num(Num),
    Var(Symbol),
}

// Manually implementing the language because the define_language macro doesn't support data variant with children, which is what the mod is being encoded as
impl Language for ModIR {
    fn matches(&self, other: &Self) -> bool {
        match (self, other) {
            (ModIR::Mod(p1, l), ModIR::Mod(p2, r)) => {
                p1 == p2 && LanguageChildren::len(l) == LanguageChildren::len(r)
            }
            (ModIR::Add(l), ModIR::Add(r)) => LanguageChildren::len(l) == LanguageChildren::len(r),
            (ModIR::Sub(l), ModIR::Sub(r)) => LanguageChildren::len(l) == LanguageChildren::len(r),
            (ModIR::Mul(l), ModIR::Mul(r)) => LanguageChildren::len(l) == LanguageChildren::len(r),
            (ModIR::Div(l), ModIR::Div(r)) => LanguageChildren::len(l) == LanguageChildren::len(r),
            (ModIR::Num(n1), ModIR::Num(n2)) => n1 == n2,
            (ModIR::Var(s1), ModIR::Var(s2)) => s1 == s2,
            _ => false,
        }
    }

    fn children(&self) -> &[Id] {
        match self {
            ModIR::Mod(_, child) => from_ref(child),
            ModIR::Add(children) => children,
            ModIR::Sub(children) => children,
            ModIR::Mul(children) => children,
            ModIR::Div(children) => children,
            ModIR::Num(_) => &[],
            ModIR::Var(_) => &[],
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        match self {
            ModIR::Mod(_, child) => from_mut(child),
            ModIR::Add(children) => children,
            ModIR::Sub(children) => children,
            ModIR::Mul(children) => children,
            ModIR::Div(children) => children,
            ModIR::Num(_) => &mut [],
            ModIR::Var(_) => &mut [],
        }
    }
}

impl FromOp for ModIR {
    type Error = ();
    fn from_op(op: &str, children: Vec<Id>) -> Result<Self, Self::Error> {
        match (op, children.as_slice()) {
            (mod_op, &[child]) if mod_op.len() > 1 && mod_op.chars().nth(0).unwrap() == '%' => {
                let mod_val: String = String::from(&mod_op[1..]);
                Ok(ModIR::Mod(mod_val, child))
            }
            ("-", &[lhs, rhs]) => Ok(ModIR::Sub([lhs, rhs])),
            ("+", &[lhs, rhs]) => Ok(ModIR::Add([lhs, rhs])),
            (number, &[]) if number.parse::<Num>().is_ok() => {
                Ok(ModIR::Num(number.parse().unwrap()))
            }
            (symbol, &[]) if symbol.parse::<Symbol>().is_ok() => {
                Ok(ModIR::Var(symbol.parse().unwrap()))
            }
            _ => Err(()),
        }
    }
}

// define_language! {
//     enum ModIR {
//         "%" = Mod(Id),      // unary mod operator to capture the bitwidth of a given sub-expression
//         Modalt(String, Id),
//         // Arithmetic operators
//         "+" = Add([Id; 2]),
//         "-" = Sub([Id; 2]),
//         "*" = Mul([Id; 2]),
//         "/" = Div([Id; 2]),
//         // Numbers
//         Num(Num),
//         // variables on which the operators operate
//         Var(Symbol),
//     }
// }

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

fn make_assoc_expr() {
    // let's try just using the language we just made
    // we'll make an e-graph with just the unit () analysis for now
    let mut egraph = EGraph::<ModIR, ModAnalysis>::default();

    let expr_a: RecExpr<ModIR> = "(%par (+ a b))".parse().unwrap();
    let var_a = egraph.add_expr(&expr_a);
    // let expr_b: RecExpr<ModIR> = "(% b)".parse().unwrap();
    // let var_b = egraph.add_expr(&expr_b);
    // let expr_c: RecExpr<ModIR> = "(% c)".parse().unwrap();
    // let var_c = egraph.add_expr(&expr_c);

    // egraph.set_analysis_data(var_a, Some(String::from("p")));
    // egraph.set_analysis_data(var_b, Some(String::from("p")));
    // egraph.set_analysis_data(var_c, Some(String::from("p")));

    println!("{:#?}", egraph);
}

fn main() {
    println!("Hello, world!");
    make_assoc_expr();
}
