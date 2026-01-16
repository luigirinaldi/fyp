use clap::error::Result;
use egg::*;
use log::warn;
use num::ToPrimitive;
use std::fmt::Debug;
use z3::ast::Bool;
use z3::ast::Int;
use z3::SatResult;
use z3::Solver;
type Num = i32;

use crate::language::apply_pow2;
use crate::language::ModIR;
use std::collections::HashMap;
use std::collections::HashSet;

// Language to describe SMT-lib parametric bitvector languages which impose a single width operator constraint
define_language! {
    pub enum ParamIR {
        "bvadd" = Add([Id; 2]),
        "bvsub" = Sub([Id; 2]),
        "bvneg" = Neg(Id),
        "bvmul" = Mul([Id; 2]),
        "bvlshr" = ShiftR([Id;2]),
        "bvshl" = ShiftL([Id;2]),
        "bvand" = And([Id;2]),
        "bvor" = Or([Id;2]),
        "bvxor" = Xor([Id;2]),
        "bvnot" = Not(Id),
        // Width manip
        "pextract" = Extract([Id; 3]), // perform bitvector extraction
        "pzero_extend" = Zext([Id; 2]), // Take an expression and the number of width to zero extend it by
        // Language to define the width expressions in the SMT-lib-esque parametric bitvector lang
        "+" = WAdd([Id; 2]),
        "-" = WSub([Id; 2]),
        "*" = WMul([Id; 2]),
        "pow2" = Pow2(Id), // power of two operator for some width cases
        // Some conditionals for good measure (handle preconditions)
        ">"  = GT([Id; 2]),
        ">=" = GTE([Id; 2]),
        "<"  = LT([Id; 2]),
        "<=" = LTE([Id; 2]),
        "=" = Eq([Id;2]),
        // Numbers and associated width expr (must be num or var)
        Num(Num, Id),
        // Variables and associate width expr (must be num or var)
        Var(Symbol, Id),
        WNum(Num),
        WVar(Symbol),
    }
}

#[derive(Debug, Default)]
pub struct ParamInfo {
    pub width_out: RecExpr<ParamIR>,
    // Vector holding the width conditions and the generated expression under those conditions
    pub expr_out: Vec<(Vec<RecExpr<ParamIR>>, RecExpr<ParamIR>)>,
}

pub fn try_join_recexpr<L, E, F>(node: &L, mut f: F) -> Result<RecExpr<L>, E>
where
    L: Language + Clone,
    F: FnMut(Id) -> Result<RecExpr<L>, E>,
{
    // 1. Compute each child RecExpr fallibly
    let parts: HashMap<Id, RecExpr<L>> = node
        .children()
        .iter()
        .copied()
        .map(|id| f(id).map(|recexpr| (id, recexpr)))
        .collect::<Result<_, _>>()?;

    // 2. Join using the existing non-fallible logic
    Ok(node
        .clone()
        .join_recexprs(|id| parts.get(&id).expect("missing child recexpr").clone()))
}

// Function that takes a modir, interpreted as a width and produces a corresponding paramir width
fn modir_w_to_paramir_w(expr: &RecExpr<ModIR>, id: Id) -> Result<RecExpr<ParamIR>, String> {
    match &expr[id] {
        ModIR::Num(num) => {
            if *num > 0 {
                Ok(RecExpr::from(vec![ParamIR::WNum(*num)]))
            } else {
                Err(format!("Constant width cannot be less than zero:{}", num))
            }
        }
        ModIR::Var(var) => Ok(RecExpr::from(vec![ParamIR::WVar(*var)])),
        ModIR::Add([a, b]) => try_join_recexpr(&ParamIR::WAdd([*a, *b]), |id| {
            modir_w_to_paramir_w(expr, id)
        }),
        ModIR::Sub([a, b]) => try_join_recexpr(&ParamIR::WSub([*a, *b]), |id| {
            modir_w_to_paramir_w(expr, id)
        }),
        ModIR::Mul([a, b]) => try_join_recexpr(&ParamIR::WMul([*a, *b]), |id| {
            modir_w_to_paramir_w(expr, id)
        }),
        ModIR::Pow([base, exp]) => {
            if expr[*base] == ModIR::Num(2) {
                try_join_recexpr(&ParamIR::Pow2(*exp), |id| modir_w_to_paramir_w(expr, id))
            } else {
                Err(format!(
                    "Only powers of two are allowed, base is: {}",
                    &expr[*base]
                ))
            }
        }
        a => Err(format!("Unkown node: {}", a)),
    }
}

pub fn modir_cond_to_paramir_cond(
    expr: &RecExpr<ModIR>,
    id: Id,
) -> Result<RecExpr<ParamIR>, String> {
    match &expr[id] {
        cond @ (ModIR::GT(_) | ModIR::GTE(_) | ModIR::LT(_) | ModIR::LTE(_)) => {
            fn opmap(modop: &ModIR) -> ParamIR {
                match modop {
                    ModIR::GT(c) => ParamIR::GT(*c),
                    ModIR::GTE(c) => ParamIR::GTE(*c),
                    ModIR::LT(c) => ParamIR::LT(*c),
                    ModIR::LTE(c) => ParamIR::LTE(*c),
                    _ => unreachable!(),
                }
            }
            try_join_recexpr(&opmap(cond), |id| modir_w_to_paramir_w(expr, id))
        }
        node => Err(format!(
            "[conv to param ir] Unsupported precondition operation {:#}",
            node
        )),
    }
}

fn case_split_binary(
    op: &str,
    w_a: &RecExpr<ParamIR>,
    expr_a: &RecExpr<ParamIR>,
    w_b: &RecExpr<ParamIR>,
    expr_b: &RecExpr<ParamIR>,
    w_out: &RecExpr<ParamIR>,
) -> Vec<(Vec<RecExpr<ParamIR>>, RecExpr<ParamIR>)> {
    if w_a.to_string() == w_b.to_string() && w_a.to_string() == w_out.to_string() {
        // shortcut for if the widths are all syntactically the same
        return vec![(vec![], format!("({op} {expr_a} {expr_b})").parse().unwrap())];
    } else {
        // all cases assuming the widths are all different
        vec![
        // width_out > max(w(a), w(b))
        (
            vec![
                format!("(> {w_out} {w_a})").parse().unwrap(),
                format!("(> {w_out} {w_b})").parse().unwrap(),
                ],
            format!("({op} (pzero_extend (- {w_out} {w_a}) {expr_a}) (pzero_extend (- {w_out} {w_b}) {expr_b}))")
                .parse()
                .unwrap(),
        ),
        // width_out = max(w(a), w(b))
        // w_o = w(a) & w(a) > w(b)
        (
            vec![
                format!("(= {w_out} {w_a})").parse().unwrap(),
                format!("(> {w_a} {w_b})").parse().unwrap(),
                ],
            format!(
                "({op} {expr_a} (pzero_extend (- {w_a} {w_b}) {expr_b})))"
            )
            .parse()
            .unwrap(),
        ),
        // w_o = w(a) & w(a) = w(b)
        (
            vec![
                format!("(= {w_out} {w_a})").parse().unwrap(),
                format!("(= {w_a} {w_b})").parse().unwrap(),
                ],
            format!(
                "({op} {expr_a} {expr_b})"
            )
            .parse()
            .unwrap(),
        ),
        // w_o = w(b) & w(a) < w(b)
        (
            vec![
                format!("(= {w_out} {w_b})").parse().unwrap(),
                format!("(< {w_a} {w_b})").parse().unwrap(),
                ],
            format!(
                "({op} (pzero_extend (- {w_b} {w_a}) {expr_a}) {expr_b})"
            )
            .parse()
            .unwrap(),
        ),
        // width_out < max(w(a), w(b))
        // w_o < w(b) & w(b) > w(a)
        (
            vec![
                format!("(< {w_out} {w_b})").parse().unwrap(),
                format!("(> {w_b} {w_a})").parse().unwrap(),
            ],
            format!(
                "(pextract (- {w_out} 1) 0 ({op} (pzero_extend (- {w_b} {w_a}) {expr_a}) {expr_b}))"
            )
            .parse()
            .unwrap(),
        )
        // w_o < w(a) & w(a) = w(b)
        ,(
            vec![
                format!("(< {w_out} {w_a})").parse().unwrap(),
                format!("(= {w_a} {w_b})").parse().unwrap(),
            ],
            format!(
                "(pextract (- {w_out} 1) 0 ({op} {expr_a} {expr_b}))"
            )
            .parse()
            .unwrap(),
        )
        // w_o < w(a) & w(a) > w(b)
        ,(
            vec![
                format!("(< {w_out} {w_a})").parse().unwrap(),
                format!("(> {w_a} {w_b})").parse().unwrap(),
            ],
            format!(
                "(pextract (- {w_out} 1) 0 ({op} {expr_a} (pzero_extend (- {w_a} {w_b}) {expr_b})))"
            )
            .parse()
            .unwrap(),
        )]
    }
}

fn case_split_unary(
    op: &str,
    w_a: &RecExpr<ParamIR>,
    expr_a: &RecExpr<ParamIR>,
    w_out: &RecExpr<ParamIR>,
) -> [(Vec<RecExpr<ParamIR>>, RecExpr<ParamIR>); 3] {
    // three cases
    // w_out > w_a
    let case_one: (Vec<RecExpr<ParamIR>>, RecExpr<ParamIR>) = (
        vec![format!("(> {w_out} {w_a})").parse().unwrap()],
        format!("({op} (pzero_extend (- {w_out} {w_a}) {expr_a}))")
            .parse()
            .unwrap(),
    );
    // w_out = w_a
    let case_two: (Vec<RecExpr<ParamIR>>, RecExpr<ParamIR>) = (
        vec![format!("(= {w_out} {w_a})").parse().unwrap()],
        format!("({op} {expr_a})").parse().unwrap(),
    );
    // w_out < w_a
    let case_three: (Vec<RecExpr<ParamIR>>, RecExpr<ParamIR>) = (
        vec![format!("(< {w_out} {w_a})").parse().unwrap()],
        format!("(pextract (- {w_out} 1) 0 ({op} {expr_a}))")
            .parse()
            .unwrap(),
    );
    [case_one, case_two, case_three]
}

/// This function takes a ModIR expression and enumerates all of the width conditions
/// in order to generate all possible combinations of width extensions and truncations
/// that would occur when performing verilog width processing.
pub fn modir_to_paramir(expr_in: &RecExpr<ModIR>, id: Id) -> Result<ParamInfo, String> {
    match &expr_in[id] {
        ModIR::Mod([w, e]) => match &expr_in[*e] {
            op @ (ModIR::Add([a, b])
            | ModIR::Mul([a, b])
            | ModIR::Sub([a, b])
            | ModIR::Or([a, b])
            | ModIR::And([a, b])
            | ModIR::Xor([a, b])
            | ModIR::ShiftL([a, b])
            | ModIR::ShiftR([a, b])) => {
                let param_op = match op {
                    ModIR::Mul(_) => "bvmul",
                    ModIR::Add(_) => "bvadd",
                    ModIR::Sub(_) => "bvsub",
                    ModIR::ShiftL(_) => "bvshl",
                    ModIR::ShiftR(_) => "bvlshr",
                    ModIR::And(_) => "bvand",
                    ModIR::Or(_) => "bvor",
                    ModIR::Xor(_) => "bvxor",
                    _ => unreachable!(),
                };

                let info_a = modir_to_paramir(expr_in, *a)?;
                let info_b = modir_to_paramir(expr_in, *b)?;

                let width_out = modir_w_to_paramir_w(expr_in, *w)?;

                let combined_exprs = info_a
                    .expr_out
                    .iter()
                    .flat_map(|(w_conds_a, expr_a)| {
                        info_b.expr_out.iter().flat_map(|(w_conds_b, expr_b)| {
                            case_split_binary(
                                param_op,
                                &info_a.width_out,
                                expr_a,
                                &info_b.width_out,
                                expr_b,
                                &width_out,
                            )
                            .iter_mut()
                            .map(|(cond, expr)| {
                                cond.append(&mut w_conds_b.clone());
                                cond.append(&mut w_conds_a.clone());
                                let cond: Vec<RecExpr<ParamIR>> = cond.to_vec();
                                let expr: RecExpr<ParamIR> = expr.clone();
                                (cond, expr)
                            })
                            .filter(|(cond, _expr)| {
                                // Filter the generated conditions to the ones that are meaningful
                                println!("{}", _expr.to_string());
                                let width_gt_zero = cond
                                    .into_iter()
                                    .flat_map(|c| c.get_width_var())
                                    .collect::<HashSet<ParamIR>>()
                                    .into_iter()
                                    .map(|w| {
                                        format!("(> {} 0)", w.to_string())
                                            .parse::<RecExpr<ParamIR>>()
                                            .unwrap()
                                    })
                                    .collect::<Vec<RecExpr<ParamIR>>>();
                                compatible_conds(cond.into_iter().chain(&width_gt_zero))
                                    .expect("Failed to evaluate condition")
                            })
                            .collect::<Vec<_>>()
                        })
                    })
                    .collect::<Vec<_>>();

                for (widths, expr) in &combined_exprs {
                    for w in widths {
                        print!("{} and", w.to_string());
                    }
                    println!(". then: {}", expr.to_string());
                }
                Ok(ParamInfo {
                    width_out,
                    expr_out: combined_exprs,
                })
            }
            op @ (ModIR::Neg(a) | ModIR::Not(a)) => {
                let info_a = modir_to_paramir(expr_in, *a)?;
                let width_out = modir_w_to_paramir_w(expr_in, *w)?;
                let op_str = match op {
                    ModIR::Neg(_) => "bvneg",
                    ModIR::Not(_) => "bvnot",
                    _ => unreachable!(),
                };
                let combined_exprs = info_a
                    .expr_out
                    .iter()
                    .flat_map(|(w_conds, expr_a)| {
                        case_split_unary(op_str, &info_a.width_out, expr_a, &width_out)
                            .iter_mut()
                            .map(|(cond, expr)| {
                                cond.append(&mut w_conds.clone());
                                (cond.to_vec(), expr.clone())
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();

                Ok(ParamInfo {
                    width_out,
                    expr_out: combined_exprs,
                })
            }
            ModIR::Var(var) => {
                let width_expr = modir_w_to_paramir_w(expr_in, *w)?;
                return Ok(ParamInfo {
                    width_out: width_expr.clone(),
                    expr_out: vec![(
                        vec![],
                        format!("({var} {})", &width_expr.to_string())
                            .parse::<RecExpr<ParamIR>>()
                            .unwrap(),
                    )],
                });
            }
            ModIR::Num(num) => {
                let width_expr = modir_w_to_paramir_w(expr_in, *w)?;
                return Ok(ParamInfo {
                    width_out: width_expr.clone(),
                    expr_out: vec![(
                        vec![],
                        format!("({num} {})", &width_expr.to_string())
                            .parse::<RecExpr<ParamIR>>()
                            .unwrap(),
                    )],
                });
            }
            ModIR::Mod(_) => todo!(),
            node => Err(format!("Invalid node type reached: {node}")),
        },
        _ => unreachable!(),
    }
}

pub trait ParamUtils {
    fn get_width_var(&self) -> HashSet<ParamIR>;
    fn get_vars(&self) -> HashSet<RecExpr<ParamIR>>;
    fn width_to_z3(&self, id: Id) -> Result<Int, String>;
    fn cond_to_z3(&self) -> Result<Bool, String>;
}

impl ParamUtils for RecExpr<ParamIR> {
    fn get_width_var(&self) -> HashSet<ParamIR> {
        self.as_ref()
            .iter()
            .map(|node| node.clone())
            .filter(|node| {
                if let ParamIR::WVar(_) = node {
                    true
                } else {
                    false
                }
            })
            .collect()
    }

    fn get_vars(&self) -> HashSet<RecExpr<ParamIR>> {
        self.as_ref()
            .iter()
            .map(|node| {
                if let ParamIR::Var(_, _) = node {
                    Some(node.build_recexpr(|id| self[id].clone()))
                } else {
                    None
                }
            })
            .filter(|x| x.is_some())
            .map(|x| x.unwrap())
            .collect()
    }

    fn cond_to_z3(&self) -> Result<Bool, String> {
        match &self[self.root()] {
            ParamIR::GT([a, b]) => Ok(self.width_to_z3(*a)?.gt(self.width_to_z3(*b)?)),
            ParamIR::GTE([a, b]) => Ok(self.width_to_z3(*a)?.ge(self.width_to_z3(*b)?)),
            ParamIR::LT([a, b]) => Ok(self.width_to_z3(*a)?.lt(self.width_to_z3(*b)?)),
            ParamIR::LTE([a, b]) => Ok(self.width_to_z3(*a)?.le(self.width_to_z3(*b)?)),
            ParamIR::Eq([a, b]) => Ok(self.width_to_z3(*a)?.eq(self.width_to_z3(*b)?)),
            _ => unreachable!("Z3 comp is not valid comparison operation: {}", self),
        }
    }

    fn width_to_z3(&self, id: Id) -> Result<Int, String> {
        match &self[id] {
            ParamIR::WVar(sym) => Ok(Int::new_const(sym.as_str())),
            ParamIR::WNum(num) => Ok(Int::from_i64(num.to_i64().unwrap())),
            ParamIR::WAdd([a, b]) => Ok(self.width_to_z3(*a)? + self.width_to_z3(*b)?),
            ParamIR::WMul([a, b]) => Ok(self.width_to_z3(*a)? * self.width_to_z3(*b)?),
            ParamIR::WSub([a, b]) => Ok(self.width_to_z3(*a)? - self.width_to_z3(*b)?),
            ParamIR::Pow2(a) => Ok(apply_pow2(&self.width_to_z3(*a)?)),
            node => Err(format!("Reached an invalid node type : {node} in {self}")),
        }
    }
}

pub fn wvar_to_smt_string(var: &ParamIR) -> String {
    match var {
        ParamIR::WVar(sym) => format!("(declare-const {sym} Int)"),
        _ => unreachable!(),
    }
}

pub fn pbvvar_to_smt_string(var: &RecExpr<ParamIR>) -> String {
    match &var[var.root()] {
        ParamIR::Var(sym, wexpr) => format!(
            "(declare-fun {sym} () (_ BitVec {}))",
            var[*wexpr].build_recexpr(|id| var[id].clone()).to_string()
        ),
        _ => unreachable!(),
    }
}

pub fn rewrite_var_to_wvar(expr: &RecExpr<ParamIR>) -> RecExpr<ParamIR> {
    let mut expr_out: RecExpr<ParamIR> = RecExpr::default();

    fn rec_call<'a>(
        expr_in: &RecExpr<ParamIR>,
        id_in: Id,
        exprout: &'a mut RecExpr<ParamIR>,
    ) -> (Id, &'a mut RecExpr<ParamIR>) {
        match &expr_in[id_in] {
            // Remove the var and replace it with a WVar so that it prints out correctly
            ParamIR::Var(sym, _w) => {
                let id = exprout.add(ParamIR::WVar(*sym));
                (id, exprout)
            }
            op => {
                let mut new_childs = HashMap::<Id, Id>::new();
                let mut expmut = exprout;
                for c_id in op.children() {
                    let (id, tmp) = rec_call(expr_in, *c_id, expmut);
                    expmut = tmp;
                    new_childs.insert(*c_id, id);
                }
                let new_op = op.clone().map_children(|i| new_childs[&i]);
                let id_out = expmut.add(new_op);
                (id_out, expmut)
            }
        }
    }

    let (_final_id, final_exp) = rec_call(expr, expr.root(), &mut expr_out);

    final_exp.clone()
}

pub fn compatible_conds<'a, I>(conds: I) -> Result<bool, String>
where
    I: IntoIterator<Item = &'a RecExpr<ParamIR>>,
{
    // Create a Z3 parameter set
    let mut params = z3::Params::new();
    params.set_u32("timeout", 100); // timeout in milliseconds
    let solver = Solver::new();
    solver.set_params(&params);

    for c in conds {
        if !c
            .as_ref()
            .into_iter()
            .any(|n| matches!(n, ParamIR::Pow2(_)))
        {
            solver.assert(c.cond_to_z3()?);
        } else {
            warn!(
                "Skipping condition because it contains a power of two: {}",
                c.to_string()
            );
        }
    }
    let res = solver.check();
    println!("Checking condition:\n{}\n{:#?}", solver.to_string(), res);
    // if res == SatResult::Sat {
    // }
    if res == SatResult::Unknown {
        Err(format!(
            "Z3 returned unkown for this problem: {}",
            solver.to_string()
        ))
    } else {
        Ok(res == SatResult::Sat)
    }
}
