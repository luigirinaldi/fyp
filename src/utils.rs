use crate::Symbol;
use egg::*;
use std::collections::HashSet;

use crate::language::ModAnalysis;
use crate::language::ModIR;

pub fn get_inferred_truths(
    egraph: &EGraph<ModIR, ModAnalysis>,
) -> Vec<(String, egg::RecExpr<ModIR>)> {
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
                // println!("found {id:?} with reason {}:\n{}", reason, expr);
                Some((String::from(just), expr))
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

pub fn get_width_vars(expr: &RecExpr<ModIR>) -> HashSet<Symbol> {
    fn get_width_rec(expr: &RecExpr<ModIR>, id: Id, is_width: bool) -> HashSet<Symbol> {
        match &expr[id] {
            ModIR::Var(s) => {
                if is_width {
                    HashSet::from([*s])
                } else {
                    HashSet::new()
                }
            }
            ModIR::Num(_) => HashSet::new(),
            ModIR::Mod([w, e]) => {
                let mut vars_w = get_width_rec(expr, *w, true);
                vars_w.extend(get_width_rec(expr, *e, false));
                vars_w
            }
            other => other
                .children()
                .into_iter()
                .map(|c| get_width_rec(expr, *c, is_width))
                .fold(HashSet::<Symbol>::new(), |mut acc, x| {
                    acc.extend(&x);
                    acc
                }),
        }
    }
    return get_width_rec(expr, expr.root(), false);
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
        val
        @ (ModIR::Mod([a, b]) | ModIR::And([a, b]) | ModIR::Or([a, b]) | ModIR::Xor([a, b])) => {
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
        ModIR::Num(num) if *num < 0 => format!("({num})"),
        op @ ModIR::Signed([w, e]) => {
            format!(
                "({} {} {})",
                op.to_string(),
                get_child_str(expr, w),
                get_child_str(expr, e)
            )
        }
        other => {
            if other.children().len() == 3 {
                format!(
                    "({} {} {} {})",
                    other.to_string(),
                    get_child_str(expr, &other.children()[0]),
                    get_child_str(expr, &other.children()[1]),
                    get_child_str(expr, &other.children()[2])
                )
            } else if other.children().len() == 2 {
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
            } else if other.children().len() == 0 {
                other.to_string()
            } else {
                panic!("Unknown operator : {}", other);
            }
        }
    }
}

pub fn sanitise_vars(expr: &RecExpr<ModIR>) -> RecExpr<ModIR> {
    let root_node: &ModIR = &expr[expr.root()];
    root_node.build_recexpr(|id| match expr[id] {
        ModIR::Var(var) => ModIR::Var(var.clone().to_string().replace("%", "var_").into()),
        _ => expr[id].clone(),
    })
}

struct FakeExplanation<L: Language> {
    /// The tree representation of the explanation.
    pub explanation_trees: TreeExplanation<L>,
    pub flat_explanation: Option<FlatExplanation<L>>,
}

pub fn check_flat_proof<'a, L, R, N>(flat_expl: FlatExplanation<L>) -> impl FnMut(R)
where
    R: IntoIterator<Item = &'a Rewrite<L, N>>,
    L: Language + 'a,
    N: Analysis<L> + 'a,
{
    let hacky_expl = FakeExplanation {
        explanation_trees: vec![],
        flat_explanation: Some(flat_expl),
    };

    let mut explanation: Explanation<L> = unsafe { std::mem::transmute(hacky_expl) };
    move |r| explanation.check_proof(r)
}
