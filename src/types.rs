use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Serialize)]
pub struct EquivalenceString {
    pub name: String,
    pub preconditions: Vec<String>,
    pub lhs: String,
    pub rhs: String,
}
