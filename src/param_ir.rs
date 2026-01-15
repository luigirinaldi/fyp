use clap::error::Result;
use egg::*;
use std::fmt::Debug;
type Num = i32;

use crate::language::ModIR;
use std::collections::HashMap;
use std::collections::HashSet;

// Language to describe SMT-lib parametric bitvector languages which impose a single width operator constraint
define_language! {
    pub enum ParamIR {
        "bvadd" = Add([Id; 2]),
        "bvneg" = Sub([Id; 2]),
        "bvsub" = Neg(Id),
        "bvmul" = Mul([Id; 2]),
        "bvlshr" = ShiftR([Id;2]),
        "bvshl" = ShiftL([Id;2]),
        "bvand" = And([Id;2]),
        "bvor" = Or([Id;2]),
        "bvxor" = Xor([Id;2]),
        "bvnot" = Not(Id),
        // Width manip
        "trunc" = Trunc([Id; 2]), // Take a target width and an expression and truncate it
        "zext" = Zext([Id; 2]), // Take an expression and the number of width to zero extend it by
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
) -> [(Vec<RecExpr<ParamIR>>, RecExpr<ParamIR>); 3] {
    // three cases,
    // width_out > max(w(a), w(b))
    let case_one: (Vec<RecExpr<ParamIR>>, RecExpr<ParamIR>) = (
        vec![
            format!("(> {w_out} {w_a})").parse().unwrap(),
            format!("(> {w_out} {w_b})").parse().unwrap(),
        ],
        format!("({op} (zext (- {w_out} {w_a}) {expr_a}) (zext (- {w_out} {w_b}) {expr_b}))")
            .parse()
            .unwrap(),
    );
    // width_out <= max(w(a), w(b)) & w(a) < w(b)
    let case_two: (Vec<RecExpr<ParamIR>>, RecExpr<ParamIR>) = (
        vec![
            format!("(<= {w_out} {w_a})").parse().unwrap(),
            format!("(<= {w_out} {w_b})").parse().unwrap(),
            format!("(< {w_a} {w_b})").parse().unwrap(),
        ],
        format!("(trunc {w_out} ({op} (zext (- {w_b} {w_a}) {expr_a}) {expr_b}))")
            .parse()
            .unwrap(),
    );
    // width_out <= max(w(a), w(b)) & w(a) >= w(b)
    let case_three: (Vec<RecExpr<ParamIR>>, RecExpr<ParamIR>) = (
        vec![
            format!("(<= {w_out} {w_a})").parse().unwrap(),
            format!("(<= {w_out} {w_b})").parse().unwrap(),
            format!("(<= {w_b} {w_a})").parse().unwrap(),
        ],
        format!("(trunc {w_out} ({op} {expr_a} (zext (- {w_a} {w_b}) {expr_b})))")
            .parse()
            .unwrap(),
    );
    [case_one, case_two, case_three]
}

fn case_split_unary(
    op: &str,
    w_a: &RecExpr<ParamIR>,
    expr_a: &RecExpr<ParamIR>,
    w_out: &RecExpr<ParamIR>,
) -> [(Vec<RecExpr<ParamIR>>, RecExpr<ParamIR>); 2] {
    // two cases
    // w_out > w_a
    let case_one: (Vec<RecExpr<ParamIR>>, RecExpr<ParamIR>) = (
        vec![format!("(> {w_out} {w_a})").parse().unwrap()],
        format!("({op} (zext (- {w_out} {w_a}) {expr_a}))")
            .parse()
            .unwrap(),
    );
    // w_out <= w_a
    let case_two: (Vec<RecExpr<ParamIR>>, RecExpr<ParamIR>) = (
        vec![format!("(<= {w_out} {w_a})").parse().unwrap()],
        format!("(trunc {w_out} ({op} {expr_a}))").parse().unwrap(),
    );
    [case_one, case_two]
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
}
