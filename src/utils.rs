use crate::Symbol;
use egg::*;
use std::collections::HashSet;
use std::fs::File;
use std::path::Path;

use crate::language::ModAnalysis;
use crate::language::ModIR;

use std::io::{Error, Write};
use std::process::{Command, Stdio};

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
                println!("found {id:?} with reason {}:\n{}", reason, expr);
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

pub fn check_isabelle_proof(proof_name: String, path: &Path) -> Result<(), Error> {
    // 1. Copy rewrite lemma file
    if let Err(e) = fs::copy(
        "./proofs/rewrite_lemmas.thy",
        path.join("rewrite_lemmas.thy"),
    ) {
        eprintln!("Failed to copy file: {}", e);
        std::process::exit(1);
    }

    // 2. Create ROOT file in the destination directory
    let root_path = path.join("ROOT");

    let mut file = match File::create(&root_path) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Failed to create ROOT file: {}", e);
            std::process::exit(1);
        }
    };

    let session_name = proof_name.clone() + "_proof";

    if let Err(e) = write!(
        file,
        "session {session_name} = HOL + theories\n  rewrite_lemmas\n  {proof_name}",
    ) {
        eprintln!("Failed to write to ROOT file: {}", e);
        std::process::exit(1);
    }

    // 3. Run bash command inside the destination directory
    println!("Checking proof with Isabelle");
    let output = Command::new("bash")
        .arg("-c")
        .arg(format!("isabelle build -v -d ./ -c {session_name}"))
        .current_dir(path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output();

    match output {
        Ok(o) => {
            if !o.status.success() {
                eprintln!("Bash command exited with an error.");
                Err(Error::other("proof couldn't be verified with isabelle"))
            } else {
                println!("Proof verified by Isabelle!");
                Ok(())
            }
        }
        Err(e) => {
            eprintln!("Failed to run bash command: {}", e);
            Err(e)
        }
    }
}
