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
    type Data = Option<(Num, PatternAst<ModIR>)>;

    fn make(egraph: &mut EGraph<ModIR, Self>, enode: &ModIR) -> Self::Data {
        // first, we make a getter function that grabs the data for a given e-class id
        let get = |id: &Id| egraph[*id].data.as_ref().map(|c| c.0);

        let result = match enode {
            ModIR::Num(n) => Some((*n, n.to_string().parse().unwrap())),
            ModIR::Add([a, b]) => {
                let a_val = get(a)?;
                let b_val = get(b)?;
                Some((
                    a_val + b_val,
                    format!("(+ {a_val} {b_val})").parse().unwrap(),
                ))
            }
            ModIR::Sub([a, b]) => {
                let a_val = get(a)?;
                let b_val = get(b)?;
                Some((
                    a_val - b_val,
                    format!("(- {a_val} {b_val})").parse().unwrap(),
                ))
            }
            ModIR::Mul([a, b]) => {
                let a_val = get(a)?;
                let b_val = get(b)?;
                Some((
                    a_val * b_val,
                    format!("(* {a_val} {b_val})").parse().unwrap(),
                ))
            }
            ModIR::Div([a_in, b_in]) => {
                let a = get(a_in)?;
                let b = get(b_in)?;
                if b != 0 {
                    Some((a.div_euclid(b), format!("({a} div {b})").parse().unwrap()))
                } else {
                    panic!("Dividing by 0! {a} div {b}")
                }
            }
            ModIR::Pow([a_id, b_id]) => {
                let a = get(a_id)?;
                let b = get(b_id)?;
                if let Some(exp) = u32::try_from(b).ok() {
                    Some((a.pow(exp), format!("(^ {a} {b})").parse().unwrap()))
                } else {
                    panic!("Found negative value in the exponent field: {b}")
                }
            }
            ModIR::Mod([width, expr]) => {
                // implement euclidean mod
                let a = get(expr)?;
                let b = get(width)?;
                let bexp = 2_i32.pow(b.to_u32()?);
                let res = a.rem_euclid(bexp);
                Some((res, format!("(bw {b} {a})").parse().unwrap()))
            }
            ModIR::Neg(id) => Some((-1 * get(id)?, format!("(- {})", get(id)?).parse().unwrap())),
            ModIR::And([a_id, b_id]) => {
                let a = get(a_id)?;
                let b = get(b_id)?;
                Some((a & b, format!("(and {a} {b})").parse().unwrap()))
            }
            ModIR::Or([a_id, b_id]) => {
                let a = get(a_id)?;
                let b = get(b_id)?;
                Some((a | b, format!("(or {a} {b})").parse().unwrap()))
            }
            ModIR::Xor([a_id, b_id]) => {
                let a = get(a_id)?;
                let b = get(b_id)?;
                Some((a ^ b, format!("(xor {a} {b})").parse().unwrap()))
            }
            ModIR::Not(id) => Some((
                -1 * get(id)? - 1,
                format!("(not {})", get(id)?).parse().unwrap(),
            )),
            ModIR::Var(_) => None,
            ModIR::Sign(_) => None,
            ModIR::ShiftR(_) => None,
            ModIR::ShiftL(_) => None,
            ModIR::GT(_) => None,
            ModIR::GTE(_) => None,
            ModIR::LT(_) => None,
            ModIR::LTE(_) => None,
            ModIR::Bool(_) => None,
        };
        result
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        merge_option(to, from, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

    fn modify(egraph: &mut EGraph<ModIR, Self>, id: Id) {
        if let Some(c) = egraph[id].data.clone() {
            egraph.union_instantiations(
                &c.1,
                &c.0.to_string().parse().unwrap(),
                &Default::default(),
                "constant_prop".to_string(),
            );
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

fn validate_width(expr: &RecExpr<ModIR>, id: Id) -> Result<(), String> {
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

fn validate_bwlang(expr: &RecExpr<ModIR>, id: Id) -> Result<(), String> {
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
    fn get_const_cond(&self) -> Result<bool, String>;
    fn get_const_width(&self, id: Id) -> Result<Num, String>;
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
    fn get_const_cond(&self) -> Result<bool, String> {
        match &self[self.root()] {
            ModIR::GT([a, b]) => Ok(self.get_const_width(*a)? > (self.get_const_width(*b)?)),
            ModIR::GTE([a, b]) => Ok(self.get_const_width(*a)? >= (self.get_const_width(*b)?)),
            ModIR::LT([a, b]) => Ok(self.get_const_width(*a)? < (self.get_const_width(*b)?)),
            ModIR::LTE([a, b]) => Ok(self.get_const_width(*a)? <= (self.get_const_width(*b)?)),
            _ => unreachable!("Z3 comp is not valid comparison operation: {}", self),
        }
    }

    fn get_const_width(&self, id: Id) -> Result<Num, String> {
        match &self[id] {
            ModIR::Var(_) => Err("Not a constant num".to_string()),
            ModIR::Num(num) => Ok(*num),
            ModIR::Add([a, b]) => Ok(self.get_const_width(*a)? + self.get_const_width(*b)?),
            ModIR::Mul([a, b]) => Ok(self.get_const_width(*a)? * self.get_const_width(*b)?),
            ModIR::Sub([a, b]) => Ok(self.get_const_width(*a)? - self.get_const_width(*b)?),
            ModIR::Pow([a, b]) => {
                if self[*a] == ModIR::Num(2) {
                    Ok(2_i32.pow(self.get_const_width(*b)?.try_into().unwrap()))
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
