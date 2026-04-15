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
) -> Result<String, String> {
    fn has_neg_num(expr: &RecExpr<ModIR>, id: Id) -> bool {
        match &expr[id] {
            ModIR::Num(n) if *n < 0 => true,
            ModIR::Not(_c) => true,
            other => other.children().iter().any(|&c| has_neg_num(expr, c)),
        }
    }

    fn rec(
        expr: &RecExpr<ModIR>,
        id: Id,
        nat_vars: &HashSet<Symbol>,
        add_type_hint: bool,
        int_nat_vars: bool,
    ) -> Result<String, String> {
        let child = |id: &Id| rec(expr, *id, nat_vars, add_type_hint, int_nat_vars);

        match &expr[id] {
            ModIR::Mod([a, b]) => {
                let int_width_vars = has_neg_num(expr, *a);
                let width_str = rec(expr, *a, nat_vars, add_type_hint, int_width_vars)?;
                let body_str = rec(expr, *b, nat_vars, add_type_hint, false)?;
                if int_width_vars {
                    Ok(format!("(bw (nat({})) {})", width_str, body_str))
                } else {
                    Ok(format!("(bw {} {})", width_str, body_str))
                }
            }
            ModIR::Var(s) if int_nat_vars && nat_vars.contains(s) => Ok(format!("int({})", s)),
            val @ (ModIR::And([a, b]) | ModIR::Or([a, b]) | ModIR::Xor([a, b])) => {
                Ok(format!("({} {} {})", val, child(a)?, child(b)?))
            }
            val @ ModIR::Pow([a, b]) if !matches!(&expr[*b], ModIR::Var(s) if nat_vars.contains(s)) => {
                Ok(format!("({} {} nat ({}))", child(a)?, val, child(b)?))
            }
            ModIR::Num(num) if add_type_hint => Ok(format!("({num}::int)")),
            ModIR::Num(num) if *num < 0 => Ok(format!("({num})")),
            op @ ModIR::Signed([w, e]) => Ok(format!("({} {} {})", op, child(w)?, child(e)?)),
            other => match other.children() {
                [a, b, c] => Ok(format!(
                    "({} {} {} {})",
                    other,
                    child(a)?,
                    child(b)?,
                    child(c)?
                )),
                [a, b] => Ok(format!("({} {} {})", child(a)?, other, child(b)?)),
                [a] => Ok(format!("({} {})", other, child(a)?)),
                [] => Ok(other.to_string()),
                _ => Err(format!("Unknown operator : {}", other)),
            },
        }
    }

    rec(expr, expr.root(), nat_vars, add_type_hint, false)
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

#[cfg(test)]
mod tests {
    use super::*;

    fn nats(vars: &[&str]) -> HashSet<Symbol> {
        vars.iter().map(|&s| Symbol::from(s)).collect()
    }

    fn p(s: &str, nat_vars: &HashSet<Symbol>, type_hint: bool) -> Result<String, String> {
        let expr: RecExpr<ModIR> = s.parse().unwrap();
        print_infix(&expr, nat_vars, type_hint)
    }

    // --- leaf nodes ---

    #[test]
    fn plain_variable() {
        assert_eq!(p("x", &nats(&[]), false), Ok("x".into()));
    }

    #[test]
    fn positive_number() {
        assert_eq!(p("5", &nats(&[]), false), Ok("5".into()));
    }

    #[test]
    fn negative_number_is_parenthesised() {
        assert_eq!(p("-1", &nats(&[]), false), Ok("(-1)".into()));
    }

    #[test]
    fn type_hint_wraps_number() {
        assert_eq!(p("5", &nats(&[]), true), Ok("(5::int)".into()));
    }

    // --- bw (Mod) width logic ---

    #[test]
    fn bw_no_neg_literal_nat_var_unmodified() {
        // width = k (no negative numeral) -> k stays as k even though it's a nat_var
        assert_eq!(p("(bw k x)", &nats(&["k"]), false), Ok("(bw k x)".into()));
    }

    #[test]
    fn bw_positive_literal_in_width_no_int_wrap() {
        // width = (k - 1): Num(1) is positive -> has_neg_num = false -> k unchanged
        assert_eq!(
            p("(bw (- k 1) x)", &nats(&["k"]), false),
            Ok("(bw (k - 1) x)".into())
        );
    }

    #[test]
    fn bw_neg_literal_in_width_wraps_nat_vars_with_int() {
        // width = (k + -1): Num(-1) triggers int_nat_vars -> k becomes int(k)
        assert_eq!(
            p("(bw (+ k -1) x)", &nats(&["k"]), false),
            Ok("(bw (nat((int(k) + (-1)))) x)".into())
        );
    }

    #[test]
    fn bw_body_never_gets_int_wrap_from_width() {
        // even though width has a negative literal, the body k stays as k
        assert_eq!(
            p("(bw (+ k -1) k)", &nats(&["k"]), false),
            Ok("(bw (nat((int(k) + (-1)))) k)".into())
        );
    }

    #[test]
    fn bw_non_nat_var_in_width_unaffected() {
        // x is not in nat_vars, so it prints as x regardless
        assert_eq!(
            p("(bw (+ x -1) y)", &nats(&[]), false),
            Ok("(bw (nat((x + (-1)))) y)".into())
        );
    }

    // --- Pow ---

    #[test]
    fn pow_nat_var_exponent_falls_to_infix_fallback() {
        // (^ 2 k) where k is a nat_var: guard fails, falls to 2-child infix
        assert_eq!(p("(^ 2 k)", &nats(&["k"]), false), Ok("(2 ^ k)".into()));
    }

    #[test]
    fn pow_non_nat_var_exponent_wrapped_with_nat() {
        // (^ 2 3): 3 is not a nat_var -> Pow arm fires with nat() wrap
        assert_eq!(p("(^ 2 3)", &nats(&[]), false), Ok("(2 ^ nat (3))".into()));
    }

    // --- explicit prefix operators (And / Or / Xor) ---

    #[test]
    fn and_is_prefix() {
        assert_eq!(p("(and x y)", &nats(&[]), false), Ok("(and x y)".into()));
    }

    #[test]
    fn or_is_prefix() {
        assert_eq!(p("(or x y)", &nats(&[]), false), Ok("(or x y)".into()));
    }

    #[test]
    fn xor_is_prefix() {
        assert_eq!(p("(xor x y)", &nats(&[]), false), Ok("(xor x y)".into()));
    }

    // --- fallback infix / prefix ---

    #[test]
    fn add_is_infix() {
        assert_eq!(p("(+ x y)", &nats(&[]), false), Ok("(x + y)".into()));
    }

    #[test]
    fn sub_is_infix() {
        assert_eq!(p("(- x y)", &nats(&[]), false), Ok("(x - y)".into()));
    }

    #[test]
    fn neg_unary_is_prefix() {
        // (- x) disambiguates to Neg(x) (1 child) -> prefix style
        assert_eq!(p("(- x)", &nats(&[]), false), Ok("(- x)".into()));
    }

    #[test]
    fn select_three_args_is_prefix() {
        assert_eq!(
            p("(sel a b c)", &nats(&[]), false),
            Ok("(sel a b c)".into())
        );
    }

    #[test]
    fn signed_op() {
        assert_eq!(
            p("(signed k x)", &nats(&[]), false),
            Ok("(signed k x)".into())
        );
    }
}
