use egg::*;
use num::ToPrimitive;
use std::fmt::Debug;
use z3::ast::{Ast, Bool, Int};
type Num = i32;
use std::collections::HashSet;

define_language! {
    pub enum ModIR {
        "bw" = Mod([Id; 2]), // mod operator to capture the bitwidth of a given sub-expression
        "@" = Sign([Id; 2]),
        // Arithmetic operators
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "-" = Neg(Id),
        "*" = Mul([Id; 2]),
        "div" = Div([Id; 2]),
        "^" = Pow([Id;2]),
        // bitvector operators
        ">>" = ShiftR([Id;2]),
        "<<" = ShiftL([Id;2]),
        "and" = And([Id;2]),
        "or" = Or([Id;2]),
        "xor" = Xor([Id;2]),
        "not" = Not([Id; 1]),
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
pub struct ModAnalysis;

impl Analysis<ModIR> for ModAnalysis {
    type Data = Option<Num>;

    fn make(egraph: &mut EGraph<ModIR, Self>, enode: &ModIR) -> Self::Data {
        // first, we make a getter function that grabs the data for a given e-class id
        let get = |id: &Id| egraph[*id].data.as_ref();

        match enode {
            ModIR::Num(n) => Some(n.clone()),
            ModIR::Add([a, b]) => Some(get(a)? + get(b)?),
            ModIR::Sub([a, b]) => Some(get(a)? - get(b)?),
            ModIR::Mul([a, b]) => Some(get(a)? * get(b)?),
            ModIR::Div([a, b]) => {
                let a = get(a)?;
                let b = *get(b)?;
                if b != 0 {
                    Some(a.div_euclid(b))
                } else {
                    None
                }
            }
            ModIR::Pow([a, b]) => {
                let a = get(a)?;
                let b = *get(b)?;
                if let Some(exp) = u32::try_from(b).ok() {
                    Some(a.pow(exp))
                } else {
                    None
                }
            }
            ModIR::Mod([a, b]) => {
                // implement euclidean mod
                let a = get(a)?;
                let b = *get(b)?;
                let bexp = 2_i32.pow(b.to_u32()?);
                Some(a.rem_euclid(bexp))
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
            egraph.union_trusted(id, id2, "constant_prop");
            // // add a mod node (only really works for positive n)
            // let min_width = (n as u32).next_power_of_two().ilog2() + 1;
            // println!("adding {} of bw {}", n, min_width as i32);
            // let bw_id = egraph.add(ModIR::Num(min_width as i32));
            // let id3 = egraph.add(ModIR::Mod([bw_id, id2]));
            // egraph.union(id, id3);
        }
    }
}

pub trait ToZ3<ModIR> {
    fn to_z3_int(&self) -> Int;
    fn to_z3_cond(&self) -> Bool;
}
fn get_recexpr(e: &RecExpr<ModIR>, id: &Id) -> RecExpr<ModIR> {
    e[*id].build_recexpr(|i| e[i].clone())
}

pub fn get_z3_variables(ast: &dyn Ast) -> Vec<String> {
    let mut vars = HashSet::new();
    collect_vars(ast, &mut vars);
    vars.into_iter().collect()
}

fn collect_vars(ast: &dyn Ast, vars: &mut HashSet<String>) {
    // If this is a variable (constant with uninterpreted function)
    if ast.num_children() == 0 && ast.decl().kind() == z3::DeclKind::UNINTERPRETED {
        vars.insert(format!("{:?}", ast));
    } else {
        // Recurse on all children
        for i in 0..ast.num_children() {
            if let Some(child) = ast.nth_child(i) {
                collect_vars(&child, vars);
            }
        }
    }
}

impl ToZ3<ModIR> for RecExpr<ModIR> {
    fn to_z3_cond(&self) -> Bool {
        let apply_comp = |a: &Id, b: &Id, op: fn(&Int, &Int) -> Bool| {
            op(
                &get_recexpr(self, a).to_z3_int(),
                &get_recexpr(self, b).to_z3_int(),
            )
        };

        match &self[self.root()] {
            ModIR::GT([a, b]) => apply_comp(a, b, |x, y| Int::gt(x, y)),
            ModIR::GTE([a, b]) => apply_comp(a, b, |x, y| Int::ge(x, y)),
            ModIR::LT([a, b]) => apply_comp(a, b, |x, y| Int::lt(x, y)),
            ModIR::LTE([a, b]) => apply_comp(a, b, |x, y| Int::le(x, y)),
            _ => unreachable!("Z3 comp is not valid comparison operation: {}", self),
        }
    }

    fn to_z3_int(&self) -> Int {
        match &self[self.root()] {
            ModIR::Var(sym) => Int::new_const(sym.as_str()),
            ModIR::Num(num) => Int::from_i64(num.to_i64().unwrap()),
            ModIR::Add([a, b]) => {
                get_recexpr(self, a).to_z3_int() + get_recexpr(self, b).to_z3_int()
            }
            ModIR::Sub([a, b]) => {
                get_recexpr(self, a).to_z3_int() - get_recexpr(self, b).to_z3_int()
            }
            ModIR::Mul([a, b]) => {
                get_recexpr(self, a).to_z3_int() * get_recexpr(self, b).to_z3_int()
            }
            ModIR::Pow([a, b]) => get_recexpr(self, a)
                .to_z3_int()
                .power(get_recexpr(self, b).to_z3_int())
                .to_int(),
            _ => unreachable!("Z3 to int is not valid int operation: {}", self),
        }
        // return Int::from_i64(0);
    }
    //     match &self[self.root()] {
    //         ModIR::Add([a,b]) =>

    //     }
    // }
}
