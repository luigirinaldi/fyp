use egg::*;
use itertools::Itertools;
use num::ToPrimitive;
use std::fmt::Debug;
type Num = i32;
use std::collections::HashSet;
use z3::ast::Ast;
use z3::{SatResult, Solver};

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

#[derive(Debug, Clone)]
pub struct SmtPBVInfo {
    pub pbv_vars: HashSet<String>,
    pub pbv_widths: HashSet<String>,
    pub width_constraints: HashSet<String>,
    pub expr: String,
    pub width: String,
}

impl SmtPBVInfo {
    pub fn zero_extend(&self, new_width: &String) -> String {
        return format!(
            "(pzero_extend (- {new_width} {}) {})",
            self.width, self.expr
        );
    }

    pub fn merge_infos(
        &self,
        other: &SmtPBVInfo,
    ) -> (HashSet<String>, HashSet<String>, HashSet<String>) {
        return (
            self.pbv_vars
                .clone()
                .into_iter()
                .chain(other.pbv_vars.clone())
                .collect(),
            self.pbv_widths
                .clone()
                .into_iter()
                .chain(other.pbv_widths.clone())
                .collect(),
            self.width_constraints
                .clone()
                .into_iter()
                .chain(other.width_constraints.clone())
                .collect(),
        );
    }

    // function to simplify the conditions, might be useful in the future
    pub fn simplify_constraints(mut self) -> Self {
        let solver = Solver::new();
        let solver_string = format!(
            "{}\n(assert (and {}))",
            self.pbv_widths
                .clone()
                .into_iter()
                .map(|w| format!("(declare-const {w} Int)"))
                .join("\n"),
            itertools::join(&self.width_constraints, " ")
        );
        solver.from_string(solver_string);
        // println!("{}", solver.to_string());
        let mut assertions = solver.get_assertions();
        let unsimplified_ast = assertions.pop().unwrap();
        let simplified_ast = unsimplified_ast.simplify();
        // println!("{}\n{:#?}", unsimplified_ast.to_string(), simplified_ast);

        // Extract individual expressions if top-level is 'and'
        let exprs: HashSet<String> = if simplified_ast.kind() == z3::AstKind::App
            && simplified_ast.decl().name().to_string() == "and"
        {
            simplified_ast
                .children()
                .iter()
                .map(|child| child.to_string())
                .collect()
        } else {
            HashSet::<String>::from([simplified_ast.to_string()])
        };
        // println!("Individual expressions:");

        self.width_constraints = exprs;
        // for expr_str in &exprs {
        //     println!("{}", expr_str);
        // }

        self
    }

    // Check whether the set of width constraints are satisfiable,
    // meaning there is a non-empty set of values for which the constraints hold
    pub fn constraints_sat(&self, extra_constraints: Option<Vec<String>>) -> bool {
        let extra_string = extra_constraints.unwrap_or(vec!["".to_string()]).join(" ");

        let solver = Solver::new();

        let width_args = self
            .pbv_widths
            .clone()
            .into_iter()
            .map(|w| format!("({w} Int)"))
            .join(" ");
        let widths_str = self.pbv_widths.clone().into_iter().join(" ");

        let solver_string = format!(
            "
(define-fun A ({width_args}) Bool
    (and
        ;; auto-gen constraints
        {}
        ;; extra condition(s)
        {extra_string})
)
(assert (exists ({width_args}) (A {widths_str})))",
            itertools::join(&self.width_constraints, " ")
        );
        // println!("{solver_string}");
        solver.from_string(solver_string);
        // print!("{}", solver.to_string());

        let res = solver.check();

        matches!(res, SatResult::Sat)
    }

    // Given two SmtPBVInfo check that the two constraints are both not trivial (not always false) and that they match
    // Take on optional extra constraints to add to both sides
    pub fn constraints_match(
        &self,
        other: &SmtPBVInfo,
        extra_constraints: Option<&Vec<String>>,
    ) -> bool {
        let solver = Solver::new();

        let (_vars, widths, _constraints) = self.merge_infos(other);

        let width_args = widths
            .clone()
            .into_iter()
            .map(|w| format!("({w} Int)"))
            .join(" ");
        let widths_str = widths.into_iter().join(" ");
        let extra_string = extra_constraints.unwrap_or(&vec!["".to_string()]).join(" ");

        let string = format!(
            "
(define-fun A ({width_args}) Bool
    (and
        ;; auto-gen constraints
        {}
        ;; provided preconditions
        {extra_string})
)
(define-fun B ({width_args}) Bool
    (and
        ;; auto-gen constraints
        {}
        ;; provided preconditions
        {extra_string})
)

;; check that both functions are satisfiable somehow
(assert (exists ({width_args}) (A {widths_str})))
(assert (exists ({width_args}) (B {widths_str})))

;; check that they are simultaneously satisfiable
(assert (exists ({width_args}) (and (A {widths_str}) (B {widths_str}))))
",
            itertools::join(&self.width_constraints, " "),
            itertools::join(&other.width_constraints, " ")
        );

        // add one of the constraints
        // println!("{}", &string);
        solver.from_string(string);
        // println!("{}", solver.to_string());
        let result = solver.check();
        // println!("{:#?}", result);

        // Check if the constraints are satisfiable (not contradictory)
        matches!(result, SatResult::Sat)
    }
}

pub trait SmtPBV {
    fn to_smt_pbv_panic(&self) -> Result<Vec<SmtPBVInfo>, String>;
    fn to_smt_pbv(&self) -> Result<Vec<SmtPBVInfo>, String>;
}

impl SmtPBV for RecExpr<ModIR> {
    fn to_smt_pbv(&self) -> Result<Vec<SmtPBVInfo>, String> {
        return match std::panic::catch_unwind(|| self.to_smt_pbv_panic()) {
            Ok(val) => val,
            Err(_) => {
                return Err(format!("modir_smt_pbv panicked for: {}", self));
            }
        }
    }

    fn to_smt_pbv_panic(&self) -> Result<Vec<SmtPBVInfo>, String> {
        let get_recexpr = |id: &Id| self[*id].build_recexpr(|id1| self[id1].clone());

        let insert_constr = |constr: &HashSet<String>, new: &String| {
            let mut c = constr.clone();
            c.insert(new.to_string());
            c
        };

        let root = &self[self.root()];

        match root {
            ModIR::Add([a, b]) | ModIR::Mul([a, b])
            // | ModIR::Sub([a, b]) 
             => {
                let a_infos = get_recexpr(&a).to_smt_pbv().unwrap();
                let b_infos = get_recexpr(&b).to_smt_pbv().unwrap();

                let out_exprs: Vec<SmtPBVInfo> = a_infos
                .into_iter()
                .cartesian_product(b_infos.into_iter())
                .flat_map(|(a_info, b_info)| {
                    let (vars, widths, constr) = a_info.clone().merge_infos(&b_info);
                    
                    let make_smtinfo = |expr, width, constr, vars, widths| SmtPBVInfo {
                        expr: expr,
                        width: width,
                        pbv_vars: vars,
                        pbv_widths: widths,
                        width_constraints: constr,
                    };

                    // model verilog semantics by zero extending the binary operation to the amount of bits required to capture the full precision
                    // then in a second step (when the mod is applied) the result is either zero extended or truncated to the outer bitwidth
                    // example:
                    //    c_r <- (a_p + b_q)_r 
                    //    if r <= p and r <= q then c_r <- (a_p)_r + (b_q)_r ; trunc both a and b to r bits
                    //    if r > p and r > q then c_r <- (zext r a_p) + (zext r b_q) ; extend a_p and b_q to r bits
                    //    etc...
                    //    so can be summarised by 
                    //    c_r <- zext/extract r ((zext a_p ((max p q) + 1)) + (zext a_p ((max p q) + 1)))
                    //    extend a and b to the width that captures the adds full precision ((max p q) + 1) and then truncate or extract more
                    let (operator, width_template) : (_, Box<dyn Fn(&SmtPBVInfo, &SmtPBVInfo) -> String>) = match root {
                        ModIR::Add(_) => ("bvadd", Box::new(|a, _b| (format!("(+ {} 1)", a.width)))),
                        ModIR::Mul(_) => ("bvmul", Box::new(|a, b|  (format!("(+ {} {})", a.width, b.width)))),
                        // ModIR::Sub(_) => ("bvsub", Box::new(|a, _b| (format!("(+ {} 1)", a.width)))), // needs zero extending?
                        _ => unreachable!("Something went wrong, proof with 0 length flat terms"),
                    };
                    let ret_smt = |x, y| format!("({operator} {} {})", x, y);
                    
                    vec![
                        (width_template(&a_info, &b_info), format!("(= {} {})", &a_info.width, &b_info.width)),
                        (width_template(&a_info, &b_info), format!("(< {} {})", &a_info.width, &b_info.width)),
                        (width_template(&a_info, &b_info), format!("(> {} {})", &a_info.width, &b_info.width))
                    ]
                    .into_iter()
                    .map(move |(new_width, condition)| 
                        make_smtinfo(
                            ret_smt(
                                a_info.zero_extend(&new_width),
                                b_info.zero_extend(&new_width)),
                            new_width,
                            insert_constr(&constr, &condition),
                            vars.clone(),
                            widths.clone()
                        ))
                    .filter(|info| info.constraints_sat(None))
                    .collect_vec()
                    })
                    .collect_vec();
                return Ok(out_exprs);
            }
            // ModIR::Neg(a) => {
            //     let child_info = get_recexpr(a).to_smt_pbv(outer_width.clone()).unwrap();

            //     if let Some(out_width) = outer_width {
            //         // if outerwidth, need to extend before negating to preserve sign bits that would otherwise be zeroed when later zeroextending
            //         return Some(SmtPBVInfo {
            //             expr: format!(
            //                 "(bvneg (pzero_extend (- (max2 {o} {w}) {w}) {e}))",
            //                 e = child_info.expr,
            //                 w = child_info.width,
            //                 o = out_width
            //             ),
            //             width: child_info.width,
            //             pbv_vars: child_info.pbv_vars,
            //             pbv_widths: child_info.pbv_widths,
            //         });
            //     } else {
            //         // if no outerwidth is provided no need to extend before negating
            //         return Some(SmtPBVInfo {
            //             expr: format!("(bvneg {})", child_info.expr),
            //             width: child_info.width,
            //             pbv_vars: child_info.pbv_vars,
            //             pbv_widths: child_info.pbv_widths,
            //         });
            //     }
            // }
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
                        return Ok(vec![SmtPBVInfo {
                            expr: label.clone(),
                            pbv_vars: HashSet::<String>::from([format!(
                                "(declare-fun {} () (_ BitVec {}))",
                                label.clone(),
                                width_str // get the string version of the width
                            )]),
                            pbv_widths: HashSet::from([width_str.clone()]),
                            width: width_str.clone(),
                            width_constraints: HashSet::<String>::from([format!(
                                "(> {} 0)",
                                width_str.clone()
                            )]),
                        }]);
                    }
                    ModIR::Num(num) => {
                        if let ModIR::Num(_) = self[*width] {
                            // the width and the value are constant, hence this is in no way parametric
                            return Ok(vec![SmtPBVInfo {
                                expr: format!("(_ bv{num} {})", width_str),
                                pbv_vars: HashSet::<String>::from([]),
                                pbv_widths: HashSet::<String>::from([]),
                                width_constraints: HashSet::<String>::from([]),
                                width: width_str,
                            }]);
                        } else {
                            // width is parametric but value isn't hence create the variable and add assert to make it equal to some val
                            let label = format!("pbv_{num}");
                            return Ok(vec![SmtPBVInfo {
                                expr: label.clone(),
                                pbv_vars: HashSet::<String>::from([format!(
                                    "(declare-fun {lab} () (_ BitVec {w}))\n(assert (= {lab} (int_to_pbv {w} {num})))",
                                    lab = label.clone(),
                                    w = width_str // get the string version of the width
                                )]),
                                pbv_widths: HashSet::from([                                    width_str.clone()
                                ]),
                                width: width_str.clone(),
                                width_constraints: HashSet::<String>::from([format!(
                                "(> {} 0)",
                                width_str.clone()
                            )]),
                            }]);
                        }
                    }
                    _ => {
                        let child_smt = get_recexpr(&term).to_smt_pbv().unwrap();

                        let ret_array: Vec<SmtPBVInfo> = child_smt
                            .into_iter()
                            .flat_map(|mut child: SmtPBVInfo| {
                                // add the new width parameter
                                child.pbv_widths.insert(width_str.clone());
                                // set it to be greater than 0
                                child
                                    .width_constraints
                                    .insert(format!("(> {} 0)", width_str.clone()));

                                return vec![
                                    SmtPBVInfo {
                                        // case where the mod width is smaller than the inner width
                                        expr: format!(
                                            "(pextract (- {} 1) 0 {})",
                                            width_str.clone(),
                                            child.expr
                                        ),
                                        pbv_vars: child.pbv_vars.clone(),
                                        pbv_widths: child.pbv_widths.clone(),
                                        width: width_str.clone(),
                                        width_constraints: insert_constr(
                                            &child.width_constraints,
                                            &format!("(< {} {})", width_str.clone(), child.width),
                                        ),
                                    },
                                    SmtPBVInfo {
                                        // case where the mod width is the same as the inner width
                                        expr: child.expr.clone(),
                                        pbv_vars: child.pbv_vars.clone(),
                                        pbv_widths: child.pbv_widths.clone(),
                                        width: width_str.clone(),
                                        width_constraints: insert_constr(
                                            &child.width_constraints,
                                            &format!("(= {} {})", width_str.clone(), child.width),
                                        ),
                                    },
                                    SmtPBVInfo {
                                        // case where the mod width is greater than inner
                                        expr: child.zero_extend(&width_str),
                                        pbv_vars: child.pbv_vars,
                                        pbv_widths: child.pbv_widths,
                                        width: width_str.clone(),
                                        width_constraints: insert_constr(
                                            &child.width_constraints,
                                            &format!("(> {} {})", width_str.clone(), child.width),
                                        ),
                                    },
                                ];
                            })
                            .filter(|info| info.constraints_sat(None))
                            .collect_vec();
                        return Ok(ret_array);
                    }
                }
            }
            _ => {
                return Err("Case not considered in match".to_string());
            }
        }
    }
}
