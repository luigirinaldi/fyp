use crate::Symbol;
use egg::*;
use std::collections::HashSet;

use crate::language::ModAnalysis;
use crate::language::ModIR;

pub fn get_inferred_truths(
    egraph: &EGraph<ModIR, ModAnalysis>,
) -> Vec<(&str, egg::RecExpr<ModIR>)> {
    let truth_id = egraph.lookup(ModIR::Bool(true)).unwrap();

    egraph
        .get_union_equalities()
        .iter()
        .cloned()
        .filter_map(move |(id1, id2, reason)| {
            let id = if id1 == truth_id {
                Some(id2)
            } else if id2 == truth_id {
                Some(id1)
            } else {
                None
            }?;

            if let Some(just) = reason.as_str().strip_prefix("inferred_") {
                let expr = egraph.id_to_expr(id);
                println!("found {id:?} with reason {}:\n{}", reason, expr);
                Some((just, expr))
            } else {
                None
            }
        })
        .collect::<Vec<_>>()
}

pub trait GetRewrite<L: Language> {
    fn get_rewrite(&self) -> (Option<Symbol>, Option<Symbol>);
}

impl<L: Language> GetRewrite<L> for FlatTerm<L> {
    fn get_rewrite(&self) -> (Option<Symbol>, Option<Symbol>) {
        if self.backward_rule.is_some() || self.forward_rule.is_some() {
            return (self.backward_rule, self.forward_rule);
        }
        let mut rewrites = self
            .children
            .iter()
            .map(|child| child.get_rewrite())
            .filter(|(back, front)| back.is_some() || front.is_some());

        let ret_val = rewrites.next();

        if let Some(next_rw) = rewrites.next() {
            println!(
                "Values left in rewrites {:#?} {:#?}",
                next_rw,
                rewrites.collect::<Vec<_>>()
            );
        }
        ret_val.unwrap_or((None, None))
    }
}

pub fn get_bitwidth_exprs(expr: &RecExpr<ModIR>) -> Vec<RecExpr<ModIR>> {
    let mut worklist = Vec::from([expr.root()]);
    let mut bw_vars: Vec<RecExpr<ModIR>> = [].to_vec();

    while !worklist.is_empty() {
        match &expr[worklist.pop().unwrap()] {
            ModIR::Mod([a, b]) => {
                bw_vars.push(expr[*a].build_recexpr(|id| expr[id].clone()));
                worklist.extend(expr[*b].children())
            }
            other => worklist.extend(other.children()),
        }
    }
    return bw_vars;
}

pub fn get_vars(expr: &RecExpr<ModIR>) -> HashSet<Symbol> {
    expr.iter()
        .filter_map(|node| {
            if let ModIR::Var(s) = node {
                Some(s.clone())
            } else {
                None
            }
        })
        .collect()
}

pub fn print_infix(
    expr: &RecExpr<ModIR>,
    nat_vars: &HashSet<Symbol>,
    add_type_hint: bool,
) -> String {
    let get_child_str = |e: &RecExpr<ModIR>, id: &Id| -> String {
        print_infix(
            &e[*id].build_recexpr(|i| e[i].clone()),
            nat_vars,
            add_type_hint,
        )
    };

    fn is_nat_var(expr: &RecExpr<ModIR>, id: &Id, nat_vars: &HashSet<Symbol>) -> bool {
        match &expr[*id] {
            ModIR::Var(symbol) => nat_vars.contains(&symbol),
            _ => false,
        }
    }

    match &expr[expr.root()] {
        val @ ModIR::Mod([a, b]) => {
            format!(
                "({} {} {})",
                val.to_string(),
                get_child_str(expr, a),
                get_child_str(expr, b)
            )
        }
        val @ ModIR::Pow([a, b]) if !is_nat_var(expr, b, nat_vars) => {
            format!(
                "({} {} nat ({}))",
                get_child_str(expr, a),
                val.to_string(),
                get_child_str(expr, b)
            )
        }
        ModIR::Num(num) if add_type_hint => format!("({num}::int)"),
        other => {
            if other.children().len() == 2 {
                format!(
                    "({} {} {})",
                    get_child_str(expr, &other.children()[0]),
                    other.to_string(),
                    get_child_str(expr, &other.children()[1])
                )
            } else if other.children().len() == 1 {
                format!(
                    "({} {})",
                    other.to_string(),
                    get_child_str(expr, &other.children()[0])
                )
            } else {
                other.to_string()
            }
        }
    }
}
