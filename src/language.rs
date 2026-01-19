use clap::error::Result;
use egg::*;
use num::ToPrimitive;
use std::fmt::Debug;
use z3::{
    ast::{Bool, Int},
    RecFuncDecl, Sort,
};
type Num = i32;

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
        "SEL" = Select([Id;3]),
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

pub fn validate_precond(expr: &RecExpr<ModIR>, id: Id) -> Result<(), String> {
    match &expr[id] {
        ModIR::GT(childs) | ModIR::GTE(childs) | ModIR::LT(childs) | ModIR::LTE(childs) => {
            childs.iter().map(|&id| validate_width(expr, id)).collect()
        }
        node => Err(format!("Unsupported precondition operation {:#}", node)),
    }
}

pub fn validate_width(expr: &RecExpr<ModIR>, id: Id) -> Result<(), String> {
    match &expr[id] {
        ModIR::Var(_) | ModIR::Num(_) => Ok(()),
        ModIR::Add(childs) | ModIR::Sub(childs) | ModIR::Mul(childs) => {
            childs.iter().map(|&id| validate_width(expr, id)).collect()
        }
        ModIR::Pow([base, exp]) => {
            if expr[*base] == ModIR::Num(2) {
                validate_width(expr, *exp)
            } else {
                Err(format!(
                    "Only powers of two are allowed, base is: {}",
                    &expr[*base]
                ))
            }
        }
        node => Err(format!(
            "Reached unsupported node while validating width expr : {:#?}",
            node
        )),
    }
}

pub fn validate_term(expr: &RecExpr<ModIR>, id: Id) -> Result<(), String> {
    match &expr[id] {
        ModIR::Mod([width, term]) => {
            validate_width(expr, *width)?;
            validate_bwlang(expr, *term)
        }
        node => Err(format!(
            "Found a child node without a 'bw' annotation: {:#?}, in {:#}",
            node, expr
        )),
    }
}

pub fn validate_bwlang(expr: &RecExpr<ModIR>, id: Id) -> Result<(), String> {
    match &expr[id] {
        ModIR::Mod([width, term]) => {
            validate_width(expr, *width)?;
            validate_bwlang(expr, *term)
        }
        ModIR::Add(childs)
        | ModIR::Sub(childs)
        | ModIR::Mul(childs)
        | ModIR::ShiftL(childs)
        | ModIR::ShiftR(childs)
        | ModIR::And(childs)
        | ModIR::Xor(childs)
        | ModIR::Or(childs) => childs.iter().map(|&id| validate_term(expr, id)).collect(),
        ModIR::Neg(child) | ModIR::Not(child) => validate_term(expr, *child),
        ModIR::Var(_) | ModIR::Num(_) => {
            if id != expr.root() {
                Ok(())
            } else {
                Err("Cannot have Var or Num as root in bwlang".to_string())
            }
        }
        node => Err(format!(
            "Found an invalid node {:#?}, in {:#?}",
            node, expr[id]
        )),
    }
}

pub trait ToZ3 {
    fn width_to_z3(&self, id: Id) -> Result<Int, String>;
    fn to_z3_cond(&self) -> Result<Bool, String>;
}

/// Apply the pow2 function to a Z3 Int
/// pow2(n) = if n == 0 then 1 else 2 * pow2(n - 1)
pub fn apply_pow2(a: &Int) -> Int {
    // Create recursive function declaration: pow2: Int -> Int
    let pow2 = RecFuncDecl::new("pow2", &[&Sort::int()], &Sort::int());

    // Create the parameter for the function body
    let n = Int::new_const("n");

    // Define the recursive body:
    // if n == 0 then 1 else 2 * pow2(n - 1)
    let zero = Int::from_i64(0);
    let one = Int::from_i64(1);
    let two = Int::from_i64(2);

    let base_case = n.eq(&zero);
    let recursive_call = pow2.apply(&[&(n.clone() - one.clone())]);
    let recursive_case = two * recursive_call.as_int().unwrap();

    let body = base_case.ite(&one, &recursive_case);

    // Add the recursive definition
    pow2.add_def(&[&n], &body);

    // Apply pow2 to the input
    pow2.apply(&[a]).as_int().unwrap()
}

impl ToZ3 for RecExpr<ModIR> {
    fn to_z3_cond(&self) -> Result<Bool, String> {
        match &self[self.root()] {
            ModIR::GT([a, b]) => Ok(self.width_to_z3(*a)?.gt(self.width_to_z3(*b)?)),
            ModIR::GTE([a, b]) => Ok(self.width_to_z3(*a)?.ge(self.width_to_z3(*b)?)),
            ModIR::LT([a, b]) => Ok(self.width_to_z3(*a)?.lt(self.width_to_z3(*b)?)),
            ModIR::LTE([a, b]) => Ok(self.width_to_z3(*a)?.le(self.width_to_z3(*b)?)),
            _ => unreachable!("Z3 comp is not valid comparison operation: {}", self),
        }
    }

    fn width_to_z3(&self, id: Id) -> Result<Int, String> {
        match &self[id] {
            ModIR::Var(sym) => Ok(Int::new_const(sym.as_str())),
            ModIR::Num(num) => Ok(Int::from_i64(num.to_i64().unwrap())),
            ModIR::Add([a, b]) => Ok(self.width_to_z3(*a)? + self.width_to_z3(*b)?),
            ModIR::Mul([a, b]) => Ok(self.width_to_z3(*a)? * self.width_to_z3(*b)?),
            ModIR::Sub([a, b]) => Ok(self.width_to_z3(*a)? - self.width_to_z3(*b)?),
            ModIR::Pow([a, b]) => {
                if self[*a] == ModIR::Num(2) {
                    Ok(apply_pow2(&self.width_to_z3(*b)?))
                } else {
                    Err(format!(
                        "Only powers of two are allowed, base is: {}",
                        &self[*a]
                    ))
                }
            }
            _ => Err("Reached an invalid node type".to_string()),
        }
    }
}
