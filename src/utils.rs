use crate::Symbol;
use egg::*;
use std::collections::HashSet;
use std::fs::File;
use std::path::Path;

use crate::language::ModAnalysis;
use crate::language::ModIR;

use std::io::{Error, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};

use regex::Regex;
use std::collections::HashMap;

use std::fs;

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

pub fn sanitise_vars(expr: &RecExpr<ModIR>) -> RecExpr<ModIR> {
    let root_node: &ModIR = &expr[expr.root()];
    root_node.build_recexpr(|id| match expr[id] {
        ModIR::Var(var) => ModIR::Var(var.clone().to_string().replace("%", "var_").into()),
        _ => expr[id].clone(),
    })
}

/// Represents a session and its failing theories
type FailingTheories = HashMap<String, Vec<String>>;

/// Process the input log, detect failing sessions, parse failing theories
fn find_failing_theories(log: &str) -> Result<FailingTheories, Error> {
    let mut result: FailingTheories = HashMap::new();

    // Regex to find lines like `{a} failed (see also "isabelle build_log -H Error {a}")`
    let failure_regex =
        Regex::new(r#"(?m)^(\w+) FAILED \(see also "isabelle build_log -H Error (\w+)"\)$"#)
            .unwrap();

    // Regex to find lines like `Theory "{a}.{b}" (in {a})`
    let theory_regex = Regex::new(r#"Theory\s+"(\w+).(\w+)"\s+\(in\s+(\w+)\):"#).unwrap();

    // Iterate over each failure match
    for cap in failure_regex.captures_iter(log) {
        let session = cap[1].to_string();
        assert!(cap[1] == cap[2], "captured session doesn't match");

        // Run `isabelle build_log -H Error {session}`
        let output = Command::new("isabelle")
            .args(["build_log", "-H", "Error", &session])
            .output();

        match output {
            Ok(o) => {
                let stdout = String::from_utf8_lossy(&o.stdout);

                // Parse output for theory failures
                for cap in theory_regex.captures_iter(&stdout) {
                    assert!(cap[1] == cap[3], "captured session doesn't match");

                    let _session_check = &cap[1];
                    let theory = cap[2].to_string();
                    // println!("Found broken theory: {theory} in session {_session_check}");
                    result.entry(session.clone()).or_default().push(theory);
                }
            }
            Err(e) => {
                eprintln!("Error found when running build_log -H for {session}");
                return Err(e);
            }
        }
    }

    Result::Ok(result)
}
