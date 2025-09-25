use egg::*;
use num::ToPrimitive;
use std::fmt::Debug;
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

#[derive(Debug)]
pub struct SmtPBVInfo {
    pub pbv_vars: HashSet<String>,
    pub pbv_widths: HashSet<String>,
    pub expr: String,
    pub width: String,
}

impl SmtPBVInfo {
    pub fn zero_extend(&self, max_width: &String) -> String {
        return format!(
            "(pzero_extend (- {max_width} {}) {})",
            self.width, self.expr
        );
    }

    pub fn merge_pbvs(self, other: SmtPBVInfo) -> (HashSet<String>, HashSet<String>) {
        return (
            self.pbv_vars.into_iter().chain(other.pbv_vars).collect(),
            self.pbv_widths
                .into_iter()
                .chain(other.pbv_widths)
                .collect(),
        );
    }
}

pub trait SmtPBV {
    fn to_smt2(&self, outer_width: Option<String>) -> Option<SmtPBVInfo>;
}

impl SmtPBV for RecExpr<ModIR> {
    fn to_smt2(&self, outer_width: Option<String>) -> Option<SmtPBVInfo> {
        let get_recexpr = |id: &Id| self[*id].build_recexpr(|id1| self[id1].clone());

        let root = &self[self.root()];

        match root {
            ModIR::Add([a, b]) | ModIR::Sub([a, b]) | ModIR::Mul([a, b]) => {
                let a_info = get_recexpr(&a).to_smt2(outer_width.clone()).unwrap();
                let b_info = get_recexpr(&b).to_smt2(outer_width.clone()).unwrap();

                let max_width: String = if let Some(out_width) = outer_width {
                    // this is the case where the outerwidth is provided
                    // here the width of each operand is extended to the max of the width of both operands or the outerwidth
                    format!("(max3 {} {} {out_width})", a_info.width, b_info.width)
                } else {
                    assert!(false);
                    format!("(max2 {} {})", a_info.width, b_info.width)
                };

                let operator = match root {
                    ModIR::Add(_) => "bvadd",
                    ModIR::Mul(_) => "bvmul",
                    ModIR::Sub(_) => "bvsub",
                    _ => unreachable!("Something went wrong, proof with 0 length flat terms"),
                };

                let ret_smt = format!(
                    "({operator} {} {})",
                    a_info.zero_extend(&max_width),
                    b_info.zero_extend(&max_width)
                );

                let (vars, widths) = a_info.merge_pbvs(b_info);

                return Some(SmtPBVInfo {
                    expr: ret_smt,
                    width: max_width,
                    pbv_vars: vars,
                    pbv_widths: widths,
                });
            }
            ModIR::Neg(a) => {
                let child_info = get_recexpr(a).to_smt2(outer_width.clone()).unwrap();

                if let Some(out_width) = outer_width {
                    // if outerwidth, need to extend before negating to preserve sign bits that would otherwise be zeroed when later zeroextending
                    return Some(SmtPBVInfo {
                        expr: format!(
                            "(bvneg (pzero_extend (- (max2 {o} {w}) {w}) {e}))",
                            e = child_info.expr,
                            w = child_info.width,
                            o = out_width
                        ),
                        width: child_info.width,
                        pbv_vars: child_info.pbv_vars,
                        pbv_widths: child_info.pbv_widths,
                    });
                } else {
                    // if no outerwidth is provided no need to extend before negating
                    return Some(SmtPBVInfo {
                        expr: format!("(bvneg {})", child_info.expr),
                        width: child_info.width,
                        pbv_vars: child_info.pbv_vars,
                        pbv_widths: child_info.pbv_widths,
                    });
                }
            }
            ModIR::Mod([width, term]) => {
                // let width_rec_expr = get_recexpr(&width);
                let width_str = match self[*width] {
                    ModIR::Num(num) => Some(num.to_string()),
                    ModIR::Var(symb) => Some(symb.to_string()),
                    _ => None,
                }
                .unwrap();
                match self[*term] {
                    ModIR::Var(symb) => {
                        // this is the case where the bw symbol identifies a parametric bitvector variable
                        let label = format!("pbv_{symb}");
                        return Some(SmtPBVInfo {
                            expr: label.clone(),
                            pbv_vars: HashSet::<String>::from([format!(
                                "(declare-fun {} () (_ BitVec {}))",
                                label.clone(),
                                width_str // get the string version of the width
                            )]),
                            pbv_widths: HashSet::from([format!(
                                "(declare-const {} Int)",
                                width_str.clone()
                            )]),
                            width: width_str,
                        });
                    }
                    ModIR::Num(num) => {
                        if let ModIR::Num(_) = self[*width] {
                            // the width and the value are constant, hence this is in no way parametric
                            return Some(SmtPBVInfo {
                                expr: format!("(_ bv{num} {})", width_str),
                                pbv_vars: HashSet::<String>::from([]),
                                pbv_widths: HashSet::<String>::from([]),
                                width: width_str,
                            });
                        } else {
                            // width is parametric but value isn't hence create the variable and add assert to make it equal to some val
                            let label = format!("pbv_{num}");
                            return Some(SmtPBVInfo {
                                expr: label.clone(),
                                pbv_vars: HashSet::<String>::from([format!(
                                    "(declare-fun {lab} () (_ BitVec {w}))\n(assert (= {lab} (int_to_pbv {w} {num})))",
                                    lab = label.clone(),
                                    w = width_str // get the string version of the width
                                )]),
                                pbv_widths: HashSet::from([format!(
                                    "(declare-const {} Int)",
                                    width_str.clone()
                                )]),
                                width: width_str,
                            });
                        }
                        // return None;
                    }
                    _ => {
                        // otherwise do nothing, pass the width downstream
                        let mut child_smt =
                            get_recexpr(&term).to_smt2(Some(width_str.clone())).unwrap();
                        child_smt
                            .pbv_widths
                            .insert(format!("(declare-const {} Int)", width_str.clone()));
                        return Some(SmtPBVInfo {
                            expr: format!(
                                "(pextract (- {} 1) 0 {})",
                                width_str.clone(),
                                child_smt.expr
                            ),
                            pbv_vars: child_smt.pbv_vars,
                            pbv_widths: child_smt.pbv_widths,
                            width: width_str,
                        });
                    }
                }
            }
            _ => {
                return None;
            }
        }
    }
}
