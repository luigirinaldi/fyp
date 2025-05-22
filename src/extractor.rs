use std::collections::HashMap;

use crate::dot_equiv::get_classes_from_root;
use crate::language::ModAnalysis;
use crate::language::ModIR;
use egg::*;

pub struct EGraphCostFn<'a> {
    egraph: &'a EGraph<ModIR, ModAnalysis>,
    shared_classes: HashMap<Id, bool>,
}

impl<'a> EGraphCostFn<'a> {
    pub fn new(
        egraph: &'a EGraph<ModIR, ModAnalysis>,
        lhs: &'a RecExpr<ModIR>,
        rhs: &'a RecExpr<ModIR>,
    ) -> Self {
        let lhs_map = get_classes_from_root(egraph, lhs);
        let rhs_map = get_classes_from_root(egraph, rhs);
        let merged: HashMap<Id, bool> = lhs_map
            .into_iter()
            .filter_map(|(key, value1)| rhs_map.get(&key).map(|&value2| (key, value1 && value2)))
            .collect();
        Self {
            egraph,
            shared_classes: merged,
        }
    }
}

impl<'a> CostFunction<ModIR> for EGraphCostFn<'a> {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &ModIR, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        // if a node is part of a shared eclass then make it cost less,
        // then in the cost minimization the extractor will favour expressions with shared enodes
        let enode_base_cost = match enode {
            // favour pure integer arithmetic expressions
            ModIR::ShiftL(_) => 200,
            ModIR::ShiftR(_) => 200,
            _ => {
                if *self
                    .shared_classes
                    .get(&self.egraph.lookup(enode.clone()).unwrap())
                    .unwrap()
                {
                    // println!("shared enode!");
                    1
                } else {
                    50
                }
            }
        };

        enode.fold(enode_base_cost, |sum, id| sum.saturating_add(costs(id)))
    }
}
